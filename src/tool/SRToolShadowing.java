package tool;

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

import java.util.List;
import java.util.stream.Collectors;

public class SRToolShadowing extends SimpleCBaseVisitor<String> {

    public SRToolShadowing() {

    }

    @Override
    public String visitProgram(ProgramContext ctx) {
        List<String> globals = ctx.globals.stream().map(this::visit).collect(Collectors.toList());
        List<String> procedures = ctx.procedures.stream().map(this::visit).collect(Collectors.toList());
        return String.join("\n", globals) + "\n" + String.join("\n", procedures);
    }

    @Override
    public String visitVarDecl(VarDeclContext ctx) {
        return "int " + ctx.ident.name.getText() + ";";
    }

    @Override
    public String visitProcedureDecl(ProcedureDeclContext ctx) {
        StringBuilder result = new StringBuilder();
        result.append("int " + ctx.name.getText() + "(");

        for (FormalParamContext formal : ctx.formals) {
            result.append(visit(formal) + ", ");
        }

        if (ctx.formals.size() != 0) {
            result.delete(result.length() - 2, result.length());
        }
        result.append(")\n");

        for (PrepostContext prepost : ctx.contract) {
            result.append("    " + visit(prepost) + ",\n");
        }

        if (ctx.contract.size() != 0) {
            result.delete(result.length() - 2, result.length());
            result.append("\n");
        }
        result.append("{\n");

        for (StmtContext stmt : ctx.stmts) {
            result.append(visit(stmt) + "\n");
        }
        result.append("return " + visit(ctx.returnExpr) + ";\n}");

        return result.toString();
    }

    @Override
    public String visitFormalParam(FormalParamContext ctx) {
        return "int " + visit(ctx.ident);
    }

    @Override
    public String visitPrepost(PrepostContext ctx) {
        StringBuilder result = new StringBuilder();
        if (ctx.requires() != null) {
            result.append(visit(ctx.requires()));
        }

        if (ctx.ensures() != null) {
            result.append(visit(ctx.ensures()));
        }

        return result.toString();
    }

    @Override
    public String visitRequires(RequiresContext ctx) {
        return "requires " + visit(ctx.condition);
    }

    @Override
    public String visitEnsures(EnsuresContext ctx) {
        return "ensures " + visit(ctx.condition);
    }

    @Override
    public String visitCandidateRequires(CandidateRequiresContext ctx) {
        return "";
    }

    @Override
    public String visitCandidateEnsures(CandidateEnsuresContext ctx) {
        return "";
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
        return visit(ctx.lhs) + " = " + visit(ctx.rhs) + ";";
    }

    @Override
    public String visitAssertStmt(AssertStmtContext ctx) {
        return "assert " + visit(ctx.condition) + ";";
    }

    @Override
    public String visitAssumeStmt(AssumeStmtContext ctx) {
        return "assume " + visit(ctx.condition) + ";";
    }

    @Override
    public String visitHavocStmt(HavocStmtContext ctx) {
        return "havoc " + visit(ctx.var) + ";";
    }

    @Override
    public String visitCallStmt(CallStmtContext ctx) {
        return "";
    }

    @Override
    public String visitIfStmt(IfStmtContext ctx) {
        StringBuilder result = new StringBuilder();
        result.append("if (" + visit(ctx.condition) + ") " + visit(ctx.thenBlock));
        if (ctx.elseBlock != null) {
            result.append(" else ");
            result.append(visit(ctx.elseBlock));
        }

        return result.toString();
    }

    @Override
    public String visitWhileStmt(WhileStmtContext ctx) {
        return "";
    }

    @Override
    public String visitBlockStmt(BlockStmtContext ctx) {
        List<String> statements = ctx.stmt().stream().map(this::visit).collect(Collectors.toList());
        return "{\n" + String.join("\n", statements) + "\n}";
    }

    @Override
    public String visitLoopInvariant(LoopInvariantContext ctx) {
        return "";
    }

    @Override
    public String visitInvariant(InvariantContext ctx) {
        return "";
    }

    @Override
    public String visitCandidateInvariant(CandidateInvariantContext ctx) {
        return "";
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
        return ternaryExpr(args);
    }

    @Override
    public String visitLorExpr(LorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> ops = ctx.ops.stream().map(t -> t.getText()).collect(Collectors.toList());
        return binaryExpr(args, ops);
    }

    @Override
    public String visitLandExpr(LandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> ops = ctx.ops.stream().map(t -> t.getText()).collect(Collectors.toList());
        return binaryExpr(args, ops);
    }

    @Override
    public String visitBorExpr(BorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> ops = ctx.ops.stream().map(t -> t.getText()).collect(Collectors.toList());
        return binaryExpr(args, ops);
    }

    @Override
    public String visitBxorExpr(BxorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> ops = ctx.ops.stream().map(t -> t.getText()).collect(Collectors.toList());
        return binaryExpr(args, ops);
    }

    @Override
    public String visitBandExpr(BandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> ops = ctx.ops.stream().map(t -> t.getText()).collect(Collectors.toList());
        return binaryExpr(args, ops);
    }

    @Override
    public String visitEqualityExpr(EqualityExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> ops = ctx.ops.stream().map(t -> t.getText()).collect(Collectors.toList());
        return binaryExpr(args, ops);
    }

    @Override
    public String visitRelExpr(RelExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> ops = ctx.ops.stream().map(t -> t.getText()).collect(Collectors.toList());
        return binaryExpr(args, ops);
    }

    @Override
    public String visitShiftExpr(ShiftExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> ops = ctx.ops.stream().map(t -> t.getText()).collect(Collectors.toList());
        return binaryExpr(args, ops);
    }

    @Override
    public String visitAddExpr(AddExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> ops = ctx.ops.stream().map(t -> t.getText()).collect(Collectors.toList());
        return binaryExpr(args, ops);
    }

    @Override
    public String visitMulExpr(MulExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> args = ctx.args.stream().map(this::visit).collect(Collectors.toList());
        List<String> ops = ctx.ops.stream().map(t -> t.getText()).collect(Collectors.toList());
        return binaryExpr(args, ops);
    }

    @Override
    public String visitUnaryExpr(UnaryExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        String arg = visit(ctx.arg);
        List<String> ops = ctx.ops.stream().map(t -> t.getText()).collect(Collectors.toList());
        return unaryOp(ops, arg);
    }

    @Override
    public String visitAtomExpr(AtomExprContext ctx) {
        if (ctx.numberExpr() != null) {
            return visit(ctx.numberExpr());
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
        return ctx.number.getText();
    }

    @Override
    public String visitVarrefExpr(VarrefExprContext ctx) {
        return visit(ctx.var);
    }

    @Override
    public String visitParenExpr(ParenExprContext ctx) {
        return "(" + visit(ctx.arg) + ")";
    }

    @Override
    public String visitResultExpr(ResultExprContext ctx) {
        return ctx.resultTok.getText() + " ";
    }

    @Override
    public String visitOldExpr(OldExprContext ctx) {
        return ctx.oldTok.getText() + "(" + visit(ctx.arg) + ")";
    }

    @Override
    public String visitVarref(VarrefContext ctx) {
        return ctx.ident.getText();
    }

    @Override
    public String visitVarIdentifier(VarIdentifierContext ctx) {
        return ctx.name.getText();
    }

    private String unaryOp(List<String> ops, String arg) {
        StringBuilder result = new StringBuilder();
        for (String op : ops) {
            result.append(op);
        }
        result.append(arg);
        return result.toString();
    }

    private static String binaryExpr(List<String> args, List<String> ops) {
        StringBuilder result = new StringBuilder();
        result.append(args.get(0));
        for (int i = 0; i < ops.size(); ++i) {
            result.append(" " + ops.get(i) + " " + args.get(i+1));
        }
        return result.toString();
    }

    private static String ternaryExpr(List<String> args) {
        StringBuilder result = new StringBuilder();
        int i = 0;
        for ( ; i < args.size() - 1; i+=2) {
            result.append(args.get(i) + " ? " + args.get(i+1) + " : ");
        }
        result.append(args.get(i));
        return result.toString();
    }
}
