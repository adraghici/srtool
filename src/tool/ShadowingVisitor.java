package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.*;

import java.util.List;
import java.util.stream.Collectors;

public class ShadowingVisitor extends SimpleCBaseVisitor<String> {
    private final Scopes scopes;

    public ShadowingVisitor() {
        scopes = Scopes.withDefault();
    }

    @Override
    public String visitProgram(ProgramContext ctx) {
        List<String> globals = ctx.globals.stream().map(this::visit).collect(Collectors.toList());
        List<String> procedures = ctx.procedures.stream().map(this::visit).collect(Collectors.toList());
        return String.join("\n", globals) + "\n" + String.join("\n", procedures);
    }

    @Override
    public String visitVarDecl(VarDeclContext ctx) {
        String var = ctx.ident.name.getText();
        scopes.declareVar(var);
        return SMTUtil.indent(scopes.count(), "int " + var + scopes.getId(var) + ";");
    }

    @Override
    public String visitProcedureDecl(ProcedureDeclContext ctx) {
        StringBuilder result = new StringBuilder();
        result.append("int " + ctx.name.getText() + "(");

        scopes.enterScope();
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
        result.append(SMTUtil.indent(scopes.count(), "return ") + visit(ctx.returnExpr) + ";\n}\n");
        scopes.exitScope();

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
        return SMTUtil.indent(scopes.count(), visit(ctx.lhs) + " = " + visit(ctx.rhs) + ";");
    }

    @Override
    public String visitAssertStmt(AssertStmtContext ctx) {
        return SMTUtil.indent(scopes.count(), "assert " + visit(ctx.condition) + ";");
    }

    @Override
    public String visitAssumeStmt(AssumeStmtContext ctx) {
        return SMTUtil.indent(scopes.count(), "assume " + visit(ctx.condition) + ";");
    }

    @Override
    public String visitHavocStmt(HavocStmtContext ctx) {
        return SMTUtil.indent(scopes.count(), "havoc " + visit(ctx.var) + ";");
    }

    @Override
    public String visitCallStmt(CallStmtContext ctx) {
        return "";
    }

    @Override
    public String visitIfStmt(IfStmtContext ctx) {
        StringBuilder result = new StringBuilder();
        result.append(SMTUtil.indent(
            scopes.count(),
            "if (" + visit(ctx.condition) + ") \n" + visit(ctx.thenBlock)));
        if (ctx.elseBlock != null) {
            result.append("\n" + SMTUtil.indent(scopes.count(), "else\n"));
            result.append(visit(ctx.elseBlock));
        }

        return result.toString();
    }

    @Override
    public String visitWhileStmt(WhileStmtContext ctx) {
        StringBuilder result = new StringBuilder();

        List<String> invariants = ctx.invariantAnnotations.stream().
            filter(i -> i.invariant() != null).map(this::visit).collect(Collectors.toList());
        List<String> candidate_invariants = ctx.invariantAnnotations.stream().
            filter(i -> i.candidateInvariant() != null).map(this::visit).collect(Collectors.toList());

        // Generate asserts.
        result.append("\n");
        for (String invariant: invariants) {
            result.append(SMTUtil.indent(scopes.count(), "assert " + invariant) + ";\n");
        }

        // TODO: Havoc modset.
        result.append("\n");

        // Generate assumes.
        for (String invariant: invariants) {
            result.append(SMTUtil.indent(scopes.count(), "assume " + invariant) + ";\n");
        }

        // Convert 'while' to 'if'.
        result.append("\n" + SMTUtil.indent(scopes.count(), "if (" + visit(ctx.condition) + ")\n"));
        result.append(visit(ctx.body));

        // Generate the asserts and the 'assume false' at the end of the 'if' body.
        // First delete the closing curly brace and then generate the new conditions.
        result.delete(result.length() - 4 * (scopes.count() - 1) - 1, result.length());
        result.append("\n");
        for (String invariant: invariants) {
            result.append(SMTUtil.indent(scopes.count() + 1, "assert " + invariant) + ";\n");
        }
        result.append(SMTUtil.indent(scopes.count() + 1, "assume 0;\n"));
        result.append(SMTUtil.indent(scopes.count(), "}"));

        return result.toString();
    }

    @Override
    public String visitBlockStmt(BlockStmtContext ctx) {
        scopes.enterScope();
        List<String> statements = ctx.stmts.stream().map(this::visit).collect(Collectors.toList());
        scopes.exitScope();

        return SMTUtil.indent(scopes.count(), "{") + "\n" +
            String.join("\n", statements) + "\n" +
            SMTUtil.indent(scopes.count(), "}");
    }

    @Override
    public String visitLoopInvariant(LoopInvariantContext ctx) {
        if (ctx.invariant() != null) {
            return visit(ctx.invariant());
        }
        return visit(ctx.candidateInvariant());
    }

    @Override
    public String visitInvariant(InvariantContext ctx) {
        return visit(ctx.expr());
    }

    @Override
    public String visitCandidateInvariant(CandidateInvariantContext ctx) {
        return visit(ctx.expr());
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
        return visit(ctx.ident);
    }

    @Override
    public String visitVarIdentifier(VarIdentifierContext ctx) {
        String var = ctx.name.getText();
        return var + scopes.getId(var);
    }

    private String unaryOp(List<String> ops, String arg) {
        StringBuilder result = new StringBuilder();
        for (String op : ops) {
            result.append(op + " ");
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
