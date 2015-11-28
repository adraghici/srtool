package visitor;

import ast.AssertStmt;
import ast.AssignStmt;
import ast.AssumeStmt;
import ast.BinaryExpr;
import ast.BlockStmt;
import ast.CallStmt;
import ast.CandidateInvariant;
import ast.CandidatePostcondition;
import ast.CandidatePrecondition;
import ast.Expr;
import ast.HavocStmt;
import ast.IfStmt;
import ast.Invariant;
import ast.LoopInvariant;
import ast.NumberExpr;
import ast.OldExpr;
import ast.ParenExpr;
import ast.Postcondition;
import ast.PrePostCondition;
import ast.Precondition;
import ast.ProcedureDecl;
import ast.Program;
import ast.ResultExpr;
import ast.Stmt;
import ast.TernaryExpr;
import ast.UnaryExpr;
import ast.VarDeclStmt;
import ast.VarRef;
import ast.VarRefExpr;
import ast.WhileStmt;
import com.google.common.base.Strings;
import ssa.Scopes;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public class CppGenVisitor extends DefaultVisitor {
    private int min;
    private int max;
    private final Scopes scopes;

    public CppGenVisitor(int min, int max) {
        this.min = min;
        this.max = max;
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
        return generateCppIncludes() + String.join("\n", globals) + "\n" + String.join("\n", procedures) + generateCppMain(program.getProcedureDecls());
    }

    @Override
    public String visit(VarDeclStmt varDeclStmt) {
        VarRef varRef = varDeclStmt.getVarRef();
        return indent(String.format("int %s = %s;", (String) varRef.accept(this), generateRandom(), (String) varRef.accept(this), (String) varRef.accept(this)));
    }

    @Override
    public String visit(ProcedureDecl procedureDecl) {
        StringBuilder result = new StringBuilder();
        scopes.enterScope();
        if (procedureDecl.getName().equals("main")) {
            // TODO: Make sure there are no clashes with other functions.
            procedureDecl.setName("_main");
        }
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
        return indent(String.format("assert(%s);", assertStmt.getCondition().accept(this)));
    }

    @Override
    public String visit(AssumeStmt assumeStmt) {
        StringBuilder result = new StringBuilder();
        // Check if assume if of the form var == expr or expr == var and use that expr instead of
        // random input.
        Expr condition = assumeStmt.getCondition();
        if (condition instanceof UnaryExpr) {
            condition = ((UnaryExpr) condition).getAtom();
        }

        if (condition instanceof ParenExpr) {
            condition = ((ParenExpr) condition).getExpr();
        }

        if (condition instanceof BinaryExpr) {
            if (((BinaryExpr) condition).getOperator().equals("==")) {
                Expr left = ((BinaryExpr) condition).getLeft();
                Expr right = ((BinaryExpr) condition).getRight();

                if (left instanceof UnaryExpr) {
                    left = ((UnaryExpr) left).getAtom();
                }

                if (right instanceof UnaryExpr) {
                    right = ((UnaryExpr) right).getAtom();
                }

                if (left instanceof VarRefExpr) {
                    return indent(String.format("%s = %s;", ((VarRefExpr) left).getVarRef().getVar(), right.accept(this)));
                } else if (right instanceof VarRefExpr) {
                    return indent(String.format("%s = %s;", ((VarRefExpr) right).getVarRef().getVar(), left.accept(this)));
                }
            }
        }

        result.append(indent(String.format("if (!(%s))\n", assumeStmt.getCondition().accept(this))));
        result.append(indent("{\n"));
        // Simply return in case assume does not hold on random input and try again later.
        result.append(indent("    return 0;\n"));
        result.append(indent("}"));
        return result.toString();
    }

    @Override
    public String visit(HavocStmt havocStmt) {
        return indent(String.format("%s = %s;", havocStmt.getVarRef().accept(this), generateRandom()));
    }

    @Override
    public String visit(CallStmt callStmt) {
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
            whileStmt.getLoopInvariants());
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

    @Override
    public String getDescription() {
        return "C++ Generator Visitor.";
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

        result.append(indent(String.format(
            "while (%s)\n%s", condition.accept(this), whileBlock.accept(this))));
        return result.toString();
    }

    private String generateCppIncludes() {
        return
            "#include <iostream>\n" +
            "#include <assert.h>\n" +
            "#include <stdlib.h>\n";
    }

    private String generateCppMain(List<ProcedureDecl> procedureDecls) {
        StringBuilder result = new StringBuilder();
        result.append("\nint main(int argc, char** argv)\n");
        result.append("{\n");
        result.append("    srand(atoi(argv[1]));\n");
        for (ProcedureDecl procedureDecl : procedureDecls) {
            // Declare and randomize input for procedure.
            for (VarRef param : procedureDecl.getParams()) {
                result.append(String.format("    int %s = %s;\n", param.getVar(), generateRandom()));
            }
            result.append(String.format("    " +
                procedureDecl.getName() +
                "(%s);\n", String.join(", ", procedureDecl.getParams().stream().map(x -> x.getVar()).collect(Collectors.toList()))));
        }
        result.append("    return 0;\n");
        result.append("}\n");
        return result.toString();
    }

    private String generateRandom() {
        int range = max - min + 1;
        return String.format("%d + rand() %% %d", min, range);
    }
}
