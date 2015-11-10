package visitor;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import org.antlr.v4.runtime.Token;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.AddExprContext;
import parser.SimpleCParser.AssertStmtContext;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.AssumeStmtContext;
import parser.SimpleCParser.AtomExprContext;
import parser.SimpleCParser.BandExprContext;
import parser.SimpleCParser.BlockStmtContext;
import parser.SimpleCParser.BorExprContext;
import parser.SimpleCParser.BxorExprContext;
import parser.SimpleCParser.CallStmtContext;
import parser.SimpleCParser.CandidateEnsuresContext;
import parser.SimpleCParser.CandidateInvariantContext;
import parser.SimpleCParser.CandidateRequiresContext;
import parser.SimpleCParser.EnsuresContext;
import parser.SimpleCParser.EqualityExprContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.FormalParamContext;
import parser.SimpleCParser.HavocStmtContext;
import parser.SimpleCParser.IfStmtContext;
import parser.SimpleCParser.InvariantContext;
import parser.SimpleCParser.LandExprContext;
import parser.SimpleCParser.LoopInvariantContext;
import parser.SimpleCParser.LorExprContext;
import parser.SimpleCParser.MulExprContext;
import parser.SimpleCParser.NumberExprContext;
import parser.SimpleCParser.OldExprContext;
import parser.SimpleCParser.ParenExprContext;
import parser.SimpleCParser.PrepostContext;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import parser.SimpleCParser.RelExprContext;
import parser.SimpleCParser.RequiresContext;
import parser.SimpleCParser.ResultExprContext;
import parser.SimpleCParser.ShiftExprContext;
import parser.SimpleCParser.StmtContext;
import parser.SimpleCParser.TernExprContext;
import parser.SimpleCParser.UnaryExprContext;
import parser.SimpleCParser.VarDeclContext;
import parser.SimpleCParser.VarIdentifierContext;
import parser.SimpleCParser.VarrefContext;
import parser.SimpleCParser.VarrefExprContext;
import parser.SimpleCParser.WhileStmtContext;
import tool.SMTUtil;
import tool.SMTUtil.Type;
import ssa.Scope;
import ssa.Scopes;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class SSAVisitor extends SimpleCBaseVisitor<String> {
    public static final String RESULT_PLACEHOLDER = "RESULT?!";
    private final List<String> postconditions;
    private final List<String> assumptions;
    private final List<String> asserts;
    private final Scopes scopes;
    private final Scopes globals;

    public SSAVisitor() {
        postconditions = Lists.newArrayList();
        assumptions = Lists.newArrayList();
        asserts = Lists.newArrayList();
        scopes = Scopes.withDefault();
        globals = Scopes.empty();
    }

    @Override
    public String visitProgram(ProgramContext ctx) {
        List<String> globals = ctx.globals.stream().map(this::visit).collect(Collectors.toList());
        List<String> procedures = ctx.procedures.stream().map(this::visit).collect(
            Collectors.toList());
        String condition = SMTUtil.generateCondition(asserts);
        return String.join("", globals) + String.join("", procedures) + condition;
    }

    @Override
    public String visitVarDecl(VarDeclContext ctx) {
        String var = ctx.ident.name.getText();
        return SMTUtil.declare(var, scopes.getId(var));
    }

    @Override
    public String visitProcedureDecl(ProcedureDeclContext ctx) {
        scopes.enterScope();
        globals.enterScope(Scope.fromScope(scopes.topScope()));
        StringBuilder result = new StringBuilder();
        for (FormalParamContext formal : ctx.formals) {
            result.append(visit(formal));
        }

        for (PrepostContext prepost : ctx.contract) {
            if (prepost.requires() != null) {
                result.append(visit(prepost));
            }
        }

        for (StmtContext stmt : ctx.stmts) {
            result.append(visit(stmt));
        }

        for (PrepostContext prepost : ctx.contract) {
            if (prepost.ensures() != null) {
                result.append(visit(prepost));
            }
        }

        String returnExpr = visit(ctx.returnExpr);
        for (String postcondition : postconditions) {
            assertion(postcondition.replace(RESULT_PLACEHOLDER, returnExpr));
        }
        scopes.exitScope();
        globals.exitScope();

        return result.toString();
    }

    @Override
    public String visitFormalParam(FormalParamContext ctx) {
        String var = ctx.ident.getText();
        return SMTUtil.declare(var, scopes.updateVar(var));
    }

    @Override
    public String visitPrepost(PrepostContext ctx) {
        StringBuilder result = new StringBuilder();
        if (ctx.requires() != null) {
            result.append(visit(ctx.requires()));
        }

        if (ctx.ensures() != null) {
            visit(ctx.ensures());
        }

        return result.toString();
    }

    @Override
    public String visitRequires(RequiresContext ctx) {
        return assume(visit(ctx.expr()));
    }

    @Override
    public String visitEnsures(EnsuresContext ctx) {
        postconditions.add(visit(ctx.condition));
        return "";
    }

    @Override
    public String visitCandidateRequires(CandidateRequiresContext ctx) {
        return null;
    }

    @Override
    public String visitCandidateEnsures(CandidateEnsuresContext ctx) {
        return null;
    }

    @Override
    public String visitStmt(StmtContext ctx) {
        if (ctx.varDecl() != null) {
            return visit(ctx.varDecl());
        }

        if (ctx.assignStmt() != null) {
            return visit(ctx.assignStmt());
        }

        if (ctx.assertStmt() != null) {
            return visit(ctx.assertStmt());
        }

        if (ctx.assumeStmt() != null) {
            return visit(ctx.assumeStmt());
        }

        if (ctx.havocStmt() != null) {
            return visit(ctx.havocStmt());
        }

        if (ctx.callStmt() != null) {
            return visit(ctx.callStmt());
        }

        if (ctx.ifStmt() != null) {
            return visit(ctx.ifStmt());
        }

        if (ctx.whileStmt() != null) {
            return visit(ctx.whileStmt());
        }

        return visit(ctx.blockStmt());
    }

    @Override
    public String visitAssignStmt(AssignStmtContext ctx) {
        String rhs = visit(ctx.rhs);
        String var = ctx.lhs.ident.name.getText();
        int id = scopes.updateVar(var);
        return SMTUtil.declare(var, id) + SMTUtil.assertion("=", var + id, rhs);
    }

    @Override
    public String visitAssertStmt(AssertStmtContext ctx) {
        String expr = visit(ctx.expr());
        return assertion(expr);
    }

    @Override
    public String visitAssumeStmt(AssumeStmtContext ctx) {
        String expr = visit(ctx.expr());
        return assume(expr);
    }

    @Override
    public String visitHavocStmt(HavocStmtContext ctx) {
        String var = ctx.var.ident.name.getText();
        return SMTUtil.declare(var, scopes.updateVar(var));
    }

    @Override
    public String visitCallStmt(CallStmtContext ctx) {
        return null;
    }

    @Override
    public String visitIfStmt(IfStmtContext ctx) {
        Scope scope = Scope.fromScope(scopes.topScope());
        String pred = SMTUtil.toBool(visit(ctx.condition));

        Scope thenScope;
        if (scope.getPred().isEmpty()) {
            thenScope = Scope.fromScope(scope, pred);
        } else {
            thenScope = Scope.fromScope(
                scope,
                SMTUtil.toBool(SMTUtil.binaryOp("and", scope.getPred(), pred)));
        }
        scopes.enterScope(thenScope);
        String thenBlock = visit(ctx.thenBlock);
        scopes.exitScope();

        Scope elseScope = Scope.fromScope(scope);
        String elseBlock = "";
        if (ctx.elseBlock != null) {
            if (scope.getPred().isEmpty()) {
                elseScope = Scope.fromScope(scope, SMTUtil.unaryOp("not", pred));
            } else {
                elseScope = Scope.fromScope(
                    scope,
                    SMTUtil.toBool(SMTUtil.binaryOp(
                        "and",
                        scope.getPred(),
                        SMTUtil.unaryOp("not", pred))));
            }
            scopes.enterScope(elseScope);
            elseBlock = visit(ctx.elseBlock);
            scopes.exitScope();
        }

        StringBuilder endIf = new StringBuilder();
        Set<String> thenModset = scope.modset(thenScope);
        Set<String> elseModset = scope.modset(elseScope);
        for (String var : Sets.union(thenModset, elseModset).immutableCopy()) {
            int thenId = thenModset.contains(var) ? thenScope.getId(var) : scope.getId(var);
            int elseId  = elseModset.contains(var) ? elseScope.getId(var) : scope.getId(var);
            endIf.append(SMTUtil.declare(var, scopes.updateVar(var)));
            endIf.append(SMTUtil.assertion(
                "=",
                var + scopes.getId(var),
                SMTUtil.ternaryOp(pred, var + thenId, var + elseId)));
        }

        return thenBlock + elseBlock + endIf;
    }

    @Override
    public String visitWhileStmt(WhileStmtContext ctx) {
        return null;
    }

    @Override
    public String visitBlockStmt(BlockStmtContext ctx) {
        scopes.enterScope();
        List<String> statements = ctx.stmt().stream().map(this::visit).collect(Collectors.toList());
        scopes.exitScope();
        return String.join("", statements);
    }

    @Override
    public String visitLoopInvariant(LoopInvariantContext ctx) {
        return null;
    }

    @Override
    public String visitInvariant(InvariantContext ctx) {
        return null;
    }

    @Override
    public String visitCandidateInvariant(CandidateInvariantContext ctx) {
        return null;
    }

    @Override
    public String visitExpr(ExprContext ctx) {
        return visit(ctx.ternExpr());
    }

    @Override
    public String visitTernExpr(TernExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        return SMTUtil.ternaryExpr(args);
    }

    @Override
    public String visitLorExpr(LorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(SSAVisitor::binaryOp).collect(Collectors.toList());
        return SMTUtil.binaryExpr(args, operators, Type.BOOL, Type.BOOL);
    }

    @Override
    public String visitLandExpr(LandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(SSAVisitor::binaryOp).collect(Collectors.toList());
        return SMTUtil.binaryExpr(args, operators, Type.BOOL, Type.BOOL);
    }

    @Override
    public String visitBorExpr(BorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(SSAVisitor::binaryOp).collect(Collectors.toList());
        return SMTUtil.binaryExpr(args, operators, Type.INT, Type.INT);
    }

    @Override
    public String visitBxorExpr(BxorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(SSAVisitor::binaryOp).collect(Collectors.toList());
        return SMTUtil.binaryExpr(args, operators, Type.INT, Type.INT);
    }

    @Override
    public String visitBandExpr(BandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(SSAVisitor::binaryOp).collect(Collectors.toList());
        return SMTUtil.binaryExpr(args, operators, Type.INT, Type.INT);
    }

    @Override
    public String visitEqualityExpr(EqualityExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(SSAVisitor::binaryOp).collect(Collectors.toList());
        return SMTUtil.binaryExpr(args, operators, Type.INT, Type.BOOL);
    }

    @Override
    public String visitRelExpr(RelExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(SSAVisitor::binaryOp).collect(Collectors.toList());
        return SMTUtil.binaryExpr(args, operators, Type.INT, Type.BOOL);
    }

    @Override
    public String visitShiftExpr(ShiftExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(SSAVisitor::binaryOp).collect(Collectors.toList());
        return SMTUtil.binaryExpr(args, operators, Type.INT, Type.INT);
    }

    @Override
    public String visitAddExpr(AddExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(SSAVisitor::binaryOp).collect(Collectors.toList());
        return SMTUtil.binaryExpr(args, operators, Type.INT, Type.INT);
    }

    @Override
    public String visitMulExpr(MulExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(SSAVisitor::binaryOp).collect(Collectors.toList());
        return SMTUtil.binaryExpr(args, operators, Type.INT, Type.INT);
    }

    @Override
    public String visitUnaryExpr(UnaryExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        String arg = visit(ctx.arg);
        List<String> operators = ctx.ops.stream().map(SSAVisitor::unaryOp).collect(Collectors.toList());

        return SMTUtil.unaryExpr(arg, operators);
    }

    @Override
    public String visitAtomExpr(AtomExprContext ctx) {
        if (ctx.numberExpr() != null) {
            return SMTUtil.number(visit(ctx.numberExpr()));
        }

        if (ctx.varrefExpr() != null) {
            return visit(ctx.varrefExpr());
        }

        if (ctx.parenExpr() != null) {
            return visit(ctx.parenExpr());
        }

        if (ctx.resultExpr() != null) {
            return visit(ctx.resultExpr());
        }

        return visit(ctx.oldExpr());
    }

    @Override
    public String visitNumberExpr(NumberExprContext ctx) {
        return ctx.NUMBER().toString();
    }

    @Override
    public String visitVarrefExpr(VarrefExprContext ctx) {
        return visit(ctx.var);
    }

    @Override
    public String visitParenExpr(ParenExprContext ctx) {
        return visit(ctx.expr());
    }

    @Override
    public String visitResultExpr(ResultExprContext ctx) {
        return RESULT_PLACEHOLDER;
    }

    @Override
    public String visitOldExpr(OldExprContext ctx) {
        String var = ctx.varref().getText();
        return var + globals.getId(var);
    }

    @Override
    public String visitVarref(VarrefContext ctx) {
        return visit(ctx.ident);
    }

    @Override
    public String visitVarIdentifier(VarIdentifierContext ctx) {
        String var = ctx.name.getText();
        return var + scopes.getId(var);
    }

    private String assertion(String expr) {
        Scope scope = scopes.topScope();
        if (scope.getPred().isEmpty()) {
            if (assumptions.isEmpty()) {
                asserts.add(expr);
            } else {
                asserts.add(SMTUtil.binaryOp(
                    "=>", SMTUtil.toBool(SMTUtil.andExpressions(assumptions)), SMTUtil.toBool(expr)));
            }
        } else if (assumptions.isEmpty()) {
            asserts.add(SMTUtil.binaryOp("=>", scope.getPred(), SMTUtil.toBool(expr)));
        } else {
            asserts.add(SMTUtil.binaryOp(
                "=>",
                SMTUtil.toBool(SMTUtil.binaryOp(
                    "and",
                    scope.getPred(),
                    SMTUtil.toBool(SMTUtil.andExpressions(assumptions)))),
                SMTUtil.toBool(expr)));
        }
        return "";
    }

    private String assume(String expr) {
        Scope scope = scopes.topScope();

        if (scope.getPred().isEmpty()) {
            assumptions.add(expr);
        } else {
            assumptions.add(SMTUtil.binaryOp("=>", scope.getPred(), SMTUtil.toBool(expr)));
        }

        return "";
    }

    private static String unaryOp(Token op) {
        return SMTUtil.unaryOp(op.getText());
    }

    private static String binaryOp(Token op) {
        return SMTUtil.binaryOp(op.getText());
    }
}
