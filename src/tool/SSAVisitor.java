package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.*;
import tool.SMTUtil.*;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class SSAVisitor extends SimpleCBaseVisitor<String> {
    private final SSAMap ssaMap;
    private final List<String> asserts;

    public SSAVisitor() {
        ssaMap = new SSAMap();
        asserts = new ArrayList<>();
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
        return SMTUtil.declare(var, ssaMap.id(var));
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
        String var = ctx.lhs.ident.name.getText();
        int id = ssaMap.fresh(var);
        String rhs = visit(ctx.rhs);

        StringBuilder result = new StringBuilder();
        result.append(SMTUtil.declare(var, id));
        result.append(SMTUtil.assertion("=", var + id, rhs));
        ssaMap.update(var, id);

        return result.toString();
    }

    @Override
    public String visitAssertStmt(AssertStmtContext ctx) {
        asserts.add(visit(ctx.expr()));
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

        StringBuilder result = new StringBuilder();
        result.append(SMTUtil.declare(var, id));
        ssaMap.update(var, id);

        return result.toString();
    }

    @Override
    public String visitCallStmt(CallStmtContext ctx) {
        return null;
    }

    @Override
    public String visitIfStmt(IfStmtContext ctx) {
        return null;
    }

    @Override
    public String visitWhileStmt(WhileStmtContext ctx) {
        return null;
    }

    @Override
    public String visitBlockStmt(BlockStmtContext ctx) {
        return null;
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
        return SMTUtil.ternaryExpression(args);
    }

    @Override
    public String visitLorExpr(LorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(op -> SMTUtil.convertBinaryOp(op.getText())).collect(Collectors.toList());
        return SMTUtil.binaryExpression(args, operators, Type.BOOL, Type.BOOL);
    }

    @Override
    public String visitLandExpr(LandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(op -> SMTUtil.convertBinaryOp(op.getText())).collect(Collectors.toList());
        return SMTUtil.binaryExpression(args, operators, Type.BOOL, Type.BOOL);
    }

    @Override
    public String visitBorExpr(BorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(op -> SMTUtil.convertBinaryOp(op.getText())).collect(Collectors.toList());
        return SMTUtil.binaryExpression(args, operators, Type.INT, Type.INT);
    }

    @Override
    public String visitBxorExpr(BxorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(op -> SMTUtil.convertBinaryOp(op.getText())).collect(Collectors.toList());
        return SMTUtil.binaryExpression(args, operators, Type.INT, Type.INT);
    }

    @Override
    public String visitBandExpr(BandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(op -> SMTUtil.convertBinaryOp(op.getText())).collect(Collectors.toList());
        return SMTUtil.binaryExpression(args, operators, Type.INT, Type.INT);
    }

    @Override
    public String visitEqualityExpr(EqualityExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(op -> SMTUtil.convertBinaryOp(op.getText())).collect(Collectors.toList());
        return SMTUtil.binaryExpression(args, operators, Type.INT, Type.BOOL);
    }

    @Override
    public String visitRelExpr(RelExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(op -> SMTUtil.convertBinaryOp(op.getText())).collect(Collectors.toList());
        return SMTUtil.binaryExpression(args, operators, Type.INT, Type.BOOL);
    }

    @Override
    public String visitShiftExpr(ShiftExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(op -> SMTUtil.convertBinaryOp(op.getText())).collect(Collectors.toList());
        return SMTUtil.binaryExpression(args, operators, Type.INT, Type.INT);
    }

    @Override
    public String visitAddExpr(AddExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(op -> SMTUtil.convertBinaryOp(op.getText())).collect(Collectors.toList());
        return SMTUtil.binaryExpression(args, operators, Type.INT, Type.INT);
    }

    @Override
    public String visitMulExpr(MulExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> operators = ctx.ops.stream().map(op -> SMTUtil.convertBinaryOp(op.getText())).collect(Collectors.toList());
        return SMTUtil.binaryExpression(args, operators, Type.INT, Type.INT);
    }

    @Override
    public String visitUnaryExpr(UnaryExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        String arg = visit(ctx.arg);
        List<String> operators = ctx.ops.stream().map(op -> SMTUtil.convertUnaryOp(op.getText())).collect(Collectors.toList());

        return SMTUtil.unaryExpression(arg, operators);
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
        StringBuilder result = new StringBuilder();

        String varName = ctx.var.ident.name.getText();
        Integer varID = ssaMap.id(varName);

        result.append(varName + varID);

        return result.toString();
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
        return null;
    }

    @Override
    public String visitVarIdentifier(VarIdentifierContext ctx) {
        return null;
    }
}
