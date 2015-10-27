package tool;

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
import tool.SMTUtil.Type;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

public class SSAVisitor extends SimpleCBaseVisitor<String> {
    private final List<String> asserts;
    private final Stack<IfTuple> ifs;
    private final SSAMap ssaMap;

    public SSAVisitor() {
        asserts = Lists.newArrayList();
        ifs = new Stack<>();
        ifs.push(new IfTuple());
        ssaMap = new SSAMap();
    }

    @Override
    public String visitProgram(ProgramContext ctx) {
        List<String> globals = ctx.globals.stream().map(this::visit).collect(Collectors.toList());
        List<String> procedures = ctx.procedures.stream().map(this::visit).collect(Collectors.toList());
        String condition = SMTUtil.generateCondition(asserts);
        return String.join("", globals) + String.join("", procedures) + condition;
    }

    @Override
    public String visitVarDecl(VarDeclContext ctx) {
        String var = ctx.ident.name.getText();
        return SMTUtil.declare(var, getCurrent(var));
    }

    @Override
    public String visitProcedureDecl(ProcedureDeclContext ctx) {
        StringBuilder result = new StringBuilder();

        for (StmtContext stmtContext : ctx.stmt()) {
            result.append(visit(stmtContext));
        }

        return result.toString();
    }

    @Override
    public String visitFormalParam(FormalParamContext ctx) {
        return null;
    }

    @Override
    public String visitPrepost(PrepostContext ctx) {
        return null;
    }

    @Override
    public String visitRequires(RequiresContext ctx) {
        return null;
    }

    @Override
    public String visitEnsures(EnsuresContext ctx) {
        return null;
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
        int id = ssaMap.fresh(var);
        updateCurrent(var, id);

        StringBuilder result = new StringBuilder();
        result.append(SMTUtil.declare(var, id));
        result.append(SMTUtil.assertion("=", var + id, rhs));
        return result.toString();
    }

    @Override
    public String visitAssertStmt(AssertStmtContext ctx) {
        String expr = visit(ctx.expr());
        if (ifs.peek().pred.isEmpty()) {
            asserts.add(expr);
        } else {
            asserts.add(SMTUtil.binaryOp("=>", ifs.peek().pred, SMTUtil.toBool(expr)));
        }
        return "";
    }

    @Override
    public String visitAssumeStmt(AssumeStmtContext ctx) {
        return null;
    }

    @Override
    public String visitHavocStmt(HavocStmtContext ctx) {
        String var = ctx.var.ident.name.getText();
        int id = ssaMap.fresh(var);
        updateCurrent(var, id);
        return SMTUtil.declare(var, id);
    }

    @Override
    public String visitCallStmt(CallStmtContext ctx) {
        return null;
    }

    @Override
    public String visitIfStmt(IfStmtContext ctx) {
        String pred = SMTUtil.toBool(visit(ctx.condition));
        Map<String, Integer> currentMap = ifs.peek().ssaMap;

        Map<String, Integer> thenMap = new HashMap<>(currentMap);
        if (ifs.peek().pred.isEmpty()) {
            ifs.push(new IfTuple(pred, thenMap));
        } else {
            ifs.push(new IfTuple(SMTUtil.toBool(
                SMTUtil.binaryOp("and", ifs.peek().pred, pred)), thenMap));
        }
        String thenBlock = visit(ctx.thenBlock);
        ifs.pop();

        Map<String, Integer> elseMap = new HashMap<>(currentMap);
        String elseBlock = "";
        if (ctx.elseBlock != null) {
            if (ifs.peek().pred.isEmpty()) {
                ifs.push(new IfTuple(SMTUtil.unaryOp("not", pred), elseMap));
            } else {
                ifs.push(
                    new IfTuple(SMTUtil.toBool(SMTUtil.binaryOp("and", ifs.peek().pred,
                        SMTUtil.unaryOp("not", pred))), elseMap));
            }
            elseBlock = visit(ctx.elseBlock);
            ifs.pop();
        }

        StringBuilder endIf = new StringBuilder();
        Set<String> thenModset = modset(currentMap, thenMap);
        Set<String> elseModset = modset(currentMap, elseMap);
        for (String var : Sets.union(thenModset, elseModset).immutableCopy()) {
            int thenId = thenModset.contains(var) ? thenMap.get(var) : getCurrent(var);
            int elseId  = elseModset.contains(var) ? elseMap.get(var) : getCurrent(var);
            int id = ssaMap.fresh(var);
            updateCurrent(var, id);
            endIf.append(SMTUtil.declare(var, id));
            endIf.append(SMTUtil.assertion(
                "=",
                var + getCurrent(var),
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
        List<String> statements = ctx.stmt().stream().map(this::visit).collect(Collectors.toList());
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
        return null;
    }

    @Override
    public String visitOldExpr(OldExprContext ctx) {
        return null;
    }

    @Override
    public String visitVarref(VarrefContext ctx) {
        String var = ctx.ident.name.getText();
        Integer id = getCurrent(var);
        return var + id;
    }

    @Override
    public String visitVarIdentifier(VarIdentifierContext ctx) {
        return null;
    }

    private void updateCurrent(String var, Integer id) {
        ifs.peek().ssaMap.put(var, id);
    }

    private Integer getCurrent(String var) {
        Map<String, Integer> map = ifs.peek().ssaMap;
        if (!map.containsKey(var)) {
            map.put(var, ssaMap.fresh(var));
        }
        return map.get(var);
    }

    private static Set<String> modset(Map<String, Integer> oldMap, Map<String, Integer> newMap) {
        return newMap.keySet().stream()
            .filter(key -> oldMap.containsKey(key) && oldMap.get(key) != newMap.get(key))
            .collect(Collectors.toSet());
    }

    private static String unaryOp(Token op) {
        return SMTUtil.unaryOp(op.getText());
    }

    private static String binaryOp(Token op) {
        return SMTUtil.binaryOp(op.getText());
    }

    private static class IfTuple {
        private String pred;
        private Map<String, Integer> ssaMap;

        public IfTuple() {
            this.pred = "";
            this.ssaMap = new HashMap<>();
        }

        public IfTuple(String pred, Map<String, Integer> ssaMap) {
            this.pred = pred;
            this.ssaMap = ssaMap;
        }
    }
}
