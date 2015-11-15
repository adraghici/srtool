package visitor;

import ast.*;
import com.google.common.base.Strings;
import ssa.Scopes;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Visitor used to print the SimpleC file held in the internal node representation.
 */
public class PrintingVisitor implements Visitor {
    private final Scopes scopes;

    public PrintingVisitor() {
        this.scopes = Scopes.withDefault();
    }

    @Override
    public String visit(Program program) {
        List<String> globals = program.getGlobalDecls().stream()
            .map(g -> (String) g.accept(this))
            .collect(Collectors.toList());
        List<String> procedures = program.getProcedureDecls().stream()
            .map(g -> (String) g.accept(this))
            .collect(Collectors.toList());
        return String.join("\n", globals) + "\n" + String.join("\n", procedures);
    }

    @Override
    public String visit(VarDeclStmt varDeclStmt) {
        VarRef varRef = varDeclStmt.getVarRef();
        return indent(String.format("int %s;", (String) varRef.accept(this)));
    }

    @Override
    public String visit(ProcedureDecl procedureDecl) {
        StringBuilder result = new StringBuilder();
        scopes.enterScope();
        result.append(formatProcedureSignature(procedureDecl.getName(), procedureDecl.getParams()));
        result.append(formatProcedureConditions(procedureDecl.getConditions()));
        result.append(formatProcedureStatements(procedureDecl.getStmts()));
        result.append(formatProcedureReturn(procedureDecl.getReturnExpr()));
        scopes.exitScope();
        return result.toString();
    }

    @Override
    public String visit(Precondition precondition) {
        return String.format("  requires %s", precondition.getCondition().accept(this));
    }

    @Override
    public String visit(Postcondition postcondition) {
        return String.format("  ensures %s", postcondition.getCondition().accept(this));
    }

    @Override
    public String visit(CandidatePrecondition candidatePrecondition) {
        return String.format(
            "  candidate_requires %s", candidatePrecondition.getCondition().accept(this));
    }

    @Override
    public String visit(CandidatePostcondition candidatePostcondition) {
        return String.format(
            "  candidate_ensures %s", candidatePostcondition.getCondition().accept(this));
    }

    @Override
    public String visit(AssignStmt assignStmt) {
        return indent(String.format(
            "%s = %s;", assignStmt.getVarRef().accept(this), assignStmt.getExpr().accept(this)));
    }

    @Override
    public String visit(AssertStmt assertStmt) {
        return indent(String.format("assert %s;", assertStmt.getCondition().accept(this)));
    }

    @Override
    public String visit(AssumeStmt assumeStmt) {
        return indent(String.format("assume %s;", assumeStmt.getCondition().accept(this)));
    }

    @Override
    public String visit(HavocStmt havocStmt) {
        return indent(String.format("havoc %s;", havocStmt.getVarRef().accept(this)));
    }

    @Override
    public Object visit(CallStmt callStmt) {
        return indent(
            String.format(
                "%s = %s;",
                callStmt.getVarRef().accept(this),
                formatProcedureCall(callStmt.getProcedureRef().getName(), callStmt.getArgs())));
    }

    @Override
    public String visit(IfStmt ifStmt) {
        return formatIfStatement(
            ifStmt.getCondition(),
            ifStmt.getThenBlock(),
            ifStmt.getElseBlock());
    }

    @Override
    public String visit(WhileStmt whileStmt) {
        return formatWhileStatement(
            whileStmt.getCondition(),
            whileStmt.getWhileBlock(),
            whileStmt.getInvariants());
    }

    @Override
    public String visit(BlockStmt blockStmt) {
        scopes.enterScope();
        String result = String.join(
            "\n",
            blockStmt.getStmts().stream()
                .map(stmt -> ((String) stmt.accept(this)))
                .collect(Collectors.toList()));
        scopes.exitScope();
        return String.format("%s\n%s\n%s", indent("{"), result, indent("}"));
    }

    @Override
    public String visit(Invariant invariant) {
        return (String) invariant.getCondition().accept(this);
    }

    @Override
    public String visit(CandidateInvariant candidateInvariant) {
        return (String) candidateInvariant.getCondition().accept(this);
    }

    @Override
    public String visit(VarRef varRef) {
        return varRef.getVar();
    }

    @Override
    public String visit(TernaryExpr ternaryExpr) {
        return String.format(
            "%s ? %s : %s",
            ternaryExpr.getCondition().accept(this),
            ternaryExpr.getTrueExpr().accept(this),
            ternaryExpr.getFalseExpr().accept(this));
    }

    @Override
    public String visit(BinaryExpr binaryExpr) {
        return String.format(
            "%s %s %s",
            binaryExpr.getLeft().accept(this),
            binaryExpr.getOperator(),
            binaryExpr.getRight().accept(this));
    }

    @Override
    public String visit(UnaryExpr unaryExpr) {
        return formatUnaryExpression(unaryExpr.getAtom(), unaryExpr.getOperators());
    }

    @Override
    public String visit(NumberExpr numberExpr) {
        return numberExpr.getNumber();
    }

    @Override
    public String visit(VarRefExpr varRefExpr) {
        return visit(varRefExpr.getVarRef());
    }

    @Override
    public String visit(ParenExpr parenExpr) {
        return String.format("(%s)", parenExpr.getExpr().accept(this));
    }

    @Override
    public String visit(ResultExpr resultExpr) {
        return resultExpr.getToken();
    }

    @Override
    public String visit(OldExpr oldExpr) {
        return String.format("\\old(%s)", oldExpr.getVarRef().accept(this));
    }

    /*
     * Format Utilities.
     */

    private String indent(String text) {
        return Strings.repeat("    ", scopes.count() - 1) + text;
    }

    private String formatProcedureSignature(String name, List<VarRef> params) {
        StringBuilder result = new StringBuilder();
        result.append(String.format("int %s(", name));
        result.append(String.join(
            ", ",
            params.stream()
                .map(p -> String.format("int %s", p.accept(this)))
                .collect(Collectors.toList())));
        result.append(")");
        return result.toString();
    }

    private String formatProcedureCall(String name, List<Expr> exprs) {
        String args = String.join(
            ", ",
            exprs.stream().map(expr -> (String) expr.accept(this)).collect(Collectors.toList()));
        return name + "(" + args + ")";
    }

    private String formatProcedureConditions(List<PrePostCondition> conditions) {
        return String.join(
            ", ",
            conditions.stream()
                .map(cond -> String.format("\n%s", cond.accept(this)))
                .collect(Collectors.toList()));
    }

    private String formatProcedureStatements(List<Stmt> stmts) {
        StringBuilder result = new StringBuilder();
        result.append("\n{\n");
        for (Stmt stmt : stmts) {
            result.append(stmt.accept(this) + "\n");
        }
        return result.toString();
    }

    private String formatProcedureReturn(Expr returnExpr) {
        return indent("return " + returnExpr.accept(this) + ";\n}\n");
    }

    private String formatUnaryExpression(Expr atom, List<String> operators) {
        StringBuilder result = new StringBuilder();
        for (String operator : operators) {
            result.append(operator + " ");
        }
        result.append((String) atom.accept(this));
        return result.toString();
    }

    private String formatIfStatement(Expr condition, BlockStmt thenBlock, Optional<BlockStmt> elseBlock) {
        StringBuilder result = new StringBuilder();
        result.append(indent(String.format("if (%s)\n%s", condition.accept(this), thenBlock.accept(this))));
        if (elseBlock.isPresent()) {
            result.append(String.format("\n%s\n%s", indent("else"), elseBlock.get().accept(this)));
        }
        return result.toString();
    }

    private String formatWhileStatement(
        Expr condition, BlockStmt whileBlock, List<LoopInvariant> loopInvariants) {
        StringBuilder result = new StringBuilder();
        String invariants = "\n" + String.join(
            ",\n",
            loopInvariants.stream()
                .map(inv -> indent((inv instanceof Invariant
                    ? "  invariant " : "  candidate_invariant ") + inv.accept(this)))
                .collect(Collectors.toList()));
        if (loopInvariants.isEmpty()) {
            invariants = "";
        }
        result.append(indent(String.format(
            "while (%s)%s\n%s", condition.accept(this), invariants, whileBlock.accept(this))));
        return result.toString();
    }
}
