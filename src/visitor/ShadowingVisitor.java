package visitor;

import ast.*;
import ssa.Scopes;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Visitor used to disambiguate variables within nested scopes.
 */
public class ShadowingVisitor implements Visitor {
    private final Scopes scopes;

    public ShadowingVisitor() {
        this.scopes = Scopes.withDefault();
    }

    @Override
    public String visit(Program program) {
        List<String> globals = program.getGlobalDecls().stream().map(g -> (String) g.accept(this)).collect(Collectors.toList());
        List<String> procedures = program.getProcedureDecls().stream().map(g -> (String) g.accept(this)).collect(Collectors.toList());
        return String.join("\n", globals) + "\n" + String.join("\n", procedures);
    }

    @Override
    public String visit(VarDeclStmt varDeclStmt) {
        VarRef varRef = varDeclStmt.getVarRef();
        scopes.declareVar(varRef.getVar());
        return String.format("int %s;", (String) varRef.accept(this));
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
    public String visit(AssignStmt assignStmt) {
        return String.format(
            "%s = %s;", assignStmt.getVarRef().accept(this), assignStmt.getExpr().accept(this));
    }

    @Override
    public String visit(AssertStmt assertStmt) {
        return String.format("assert %s;", assertStmt.getCondition().accept(this));
    }

    @Override
    public String visit(AssumeStmt assumeStmt) {
        return String.format("assume %s;", assumeStmt.getCondition().accept(this));
    }

    @Override
    public String visit(HavocStmt havocStmt) {
        return String.format("havoc %s;", havocStmt.getVarRef().accept(this));
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
        return String.format("{\n%s\n}", result);
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
        return getShadowedVar(varRef.getVar());
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

    private String formatProcedureSignature(String name, List<VarRef> params) {
        StringBuilder result = new StringBuilder();
        result.append(String.format("int %s(", name));
        for (VarRef param : params) {
            result.append(String.format("int %s, ", param.accept(this)));
        }
        // In case the procedure has parameters, remove the extra comma and space at the end.
        if (!params.isEmpty()) {
            result.delete(result.length() - 2, result.length());
        }
        result.append(")");
        return result.toString();
    }

    private String formatProcedureConditions(List<PrePostCondition> conditions) {
        StringBuilder result = new StringBuilder();
        for (PrePostCondition prePostCondition : conditions) {
            result.append(String.format("%s,\n", prePostCondition.accept(this)));
        }
        if (!conditions.isEmpty()) {
            result.delete(result.length() - 2, result.length());
        }
        return result.toString();
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
        return "return " + returnExpr.accept(this) + ";\n}\n";
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
        result.append(String.format("if (%s)\n%s", condition.accept(this), thenBlock.accept(this)));
        if (elseBlock.isPresent()) {
            result.append(String.format("\nelse\n%s", elseBlock.get().accept(this)));
        }
        return result.toString();
    }

    private String formatWhileStatement(
        Expr condition, BlockStmt whileBlock, List<LoopInvariant> loopInvariants) {
        StringBuilder result = new StringBuilder();
        String invariants = String.join(
            ",\n",
            loopInvariants.stream()
                .map(inv -> (inv instanceof Invariant ? "invariant " : "candidate_invariant ") + inv.accept(this))
                .collect(Collectors.toList()));
        result.append(
            String.format("while (%s)\n%s\n%s", condition.accept(this), invariants, whileBlock.accept(this)));
        return result.toString();
    }

    private String getShadowedVar(String var) {
        return var + this.scopes.getId(var);
    }
}
