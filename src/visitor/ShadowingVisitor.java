package visitor;

import ast.*;
import ssa.Scopes;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public class ShadowingVisitor implements ASTVisitor {

    private final Scopes scopes;

    public ShadowingVisitor() {
        this.scopes = Scopes.withDefault();
    }

    @Override
    public String visit(AssertStmt assertStmt) {
        return String.format("assert %s;", visit(assertStmt.getCondition()));
    }

    @Override
    public String visit(AssignStmt assignStmt) {
        return String.format("%s = %s;", getShadowedVar(assignStmt.getVar()),visit(assignStmt.getExpr()));
    }

    @Override
    public String visit(AssumeStmt assumeStmt) {
        return String.format("assume %s;", visit(assumeStmt.getCondition()));
    }

    @Override
    public String visit(AtomExpr atomExpr) {
        if (atomExpr instanceof NumberExpr) {
            return visit((NumberExpr) atomExpr);
        } else if (atomExpr instanceof VarRefExpr) {
            return visit((VarRefExpr) atomExpr);
        } else if (atomExpr instanceof ParenExpr) {
            return visit((ParenExpr) atomExpr);
        } else if (atomExpr instanceof ResultExpr) {
            return visit((ResultExpr) atomExpr);
        } else {
            return visit((OldExpr) atomExpr);
        }
    }

    @Override
    public String visit(BinaryExpr binaryExpr) {
        return String.format("%s %s %s",
            visit(binaryExpr.getLeft()), binaryExpr.getOperator(), visit(binaryExpr.getRight()));
    }

    @Override
    public String visit(BlockStmt blockStmt) {
        scopes.enterScope();
        String result = String.join("\n",
            blockStmt.getStmts().stream().map(this::visit).collect(Collectors.toList()));
        scopes.exitScope();
        return String.format("{\n%s\n}", result);
    }

    @Override
    public String visit(CandidatePostcondition candidatePostcondition) {
        return "";
    }

    @Override
    public String visit(CandidatePrecondition candidatePrecondition) {
        return "";
    }

    @Override
    public String visit(Expr expr) {
        if (expr instanceof TernaryExpr) {
            return visit((TernaryExpr) expr);
        } else if (expr instanceof BinaryExpr) {
            return visit((BinaryExpr) expr);
        } else if (expr instanceof UnaryExpr) {
            return visit((UnaryExpr) expr);
        } else {
            return visit((AtomExpr) expr);
        }
    }

    @Override
    public String visit(HavocStmt havocStmt) {
        return String.format("havoc %s;", getShadowedVar(havocStmt.getVar()));
    }

    @Override
    public String visit(IfStmt ifStmt) {
        return formatIfStatement(ifStmt.getCondition(), ifStmt.getThenBlock(), ifStmt.getElseBlock());
    }

    @Override
    public String visit(NumberExpr numberExpr) {
        return numberExpr.getNumber();
    }

    @Override
    public String visit(OldExpr oldExpr) {
        return String.format("\\old(%s)", getShadowedVar(oldExpr.getVar()));
    }

    @Override
    public String visit(ParenExpr parenExpr) {
        return String.format("(%s)", visit(parenExpr.getExpr()));
    }

    @Override
    public String visit(Postcondition postcondition) {
        return String.format("  ensures %s", visit(postcondition.getCondition()));
    }

    @Override
    public String visit(Precondition precondition) {
        return String.format("  requires %s", visit(precondition.getCondition()));
    }

    @Override
    public String visit(PrePostCondition prePostCondition) {
        if (prePostCondition instanceof Postcondition) {
            return visit((Postcondition) prePostCondition);
        } else if (prePostCondition instanceof Precondition) {
            return visit((Precondition) prePostCondition);
        } else if (prePostCondition instanceof CandidatePostcondition) {
            return visit((CandidatePostcondition) prePostCondition);
        } else {
            return visit((CandidatePrecondition) prePostCondition);
        }
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
    public String visit(Program program) {
        List<String> globals = program.getGlobalDecls().stream().map(this::visit).collect(Collectors.toList());
        List<String> procedures = program.getProcedureDecls().stream().map(this::visit).collect(Collectors.toList());
        return String.join("\n", globals) + "\n" + String.join("\n", procedures);
    }

    @Override
    public String visit(ResultExpr resultExpr) {
        return resultExpr.getToken();
    }

    @Override
    public String visit(Stmt stmt) {
        if (stmt instanceof VarDeclStmt) {
            return visit((VarDeclStmt) stmt);
        } else if (stmt instanceof AssignStmt) {
            return visit((AssignStmt) stmt);
        } else if (stmt instanceof AssertStmt) {
            return visit((AssertStmt) stmt);
        } else if (stmt instanceof AssumeStmt) {
            return visit((AssumeStmt) stmt);
        } else if (stmt instanceof HavocStmt) {
            return visit((HavocStmt) stmt);
        } else if (stmt instanceof IfStmt) {
            return visit((IfStmt) stmt);
        } else {
            return visit((BlockStmt) stmt);
        }
    }

    @Override
    public String visit(TernaryExpr ternaryExpr) {
        return String.format("%s ? %s : %s",
            visit(ternaryExpr.getCondition()),
            visit(ternaryExpr.getTrueExpr()),
            visit(ternaryExpr.getFalseExpr()));
    }

    @Override
    public String visit(UnaryExpr unaryExpr) {
        return formatUnaryExpression(unaryExpr.getAtom(), unaryExpr.getOperators());
    }

    @Override
    public String visit(VarDeclStmt varDeclStmt) {
        String var = varDeclStmt.getVar();
        scopes.declareVar(var);
        return String.format("int %s;", getShadowedVar(var));
    }

    @Override
    public String visit(VarRefExpr varRefExpr) {
        return getShadowedVar(varRefExpr.getVar());
    }

    /*
     * Format Utilities.
     */

    private String formatProcedureSignature(String name, List<String> params) {
        StringBuilder result = new StringBuilder();
        result.append(String.format("int %s(", name));
        for (String param : params) {
            result.append(String.format("int %s, ", getShadowedVar(param)));
        }
        // In case the procedure has parameters, remove the extra comma and space at the end.
        if (!params.isEmpty()) {
            result.delete(result.length() - 2, result.length());
        }
        result.append(")\n");
        return result.toString();
    }

    private String formatProcedureConditions(List<PrePostCondition> conditions) {
        StringBuilder result = new StringBuilder();
        for (PrePostCondition prePostCondition : conditions) {
            result.append(String.format("%s,\n", visit(prePostCondition)));
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
            result.append(visit(stmt) + "\n");
        }
        return result.toString();
    }

    private String formatProcedureReturn(Expr returnExpr) {
        return "return " + visit(returnExpr) + ";\n}\n";
    }

    private String formatUnaryExpression(Expr atom, List<String> operators) {
        StringBuilder result = new StringBuilder();
        for (String operator : operators) {
            result.append(operator + " ");
        }
        result.append(visit(atom));
        return result.toString();
    }

    private String formatIfStatement(Expr condition, BlockStmt thenBlock, Optional<BlockStmt> elseBlock) {
        StringBuilder result = new StringBuilder();
        result.append(String.format("if (%s)\n%s", visit(condition), visit(thenBlock)));
        if (elseBlock.isPresent()) {
            result.append(String.format("\nelse\n%s", visit(elseBlock.get())));
        }
        return result.toString();
    }

    private String getShadowedVar(String var) {
        return var + this.scopes.getId(var);
    }
}
