package visitor;

import ast.*;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import ssa.Scope;
import ssa.Scopes;
import tool.SMTUtil;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class ASTSSAVisitor implements ASTVisitor {
    public static final String RESULT_PLACEHOLDER = "RESULT?!";
    private final List<String> postconditions;
    private final List<String> assumptions;
    private final List<String> asserts;
    private final Scopes scopes;
    private final Scopes globals;

    public ASTSSAVisitor() {
        postconditions = Lists.newArrayList();
        assumptions = Lists.newArrayList();
        asserts = Lists.newArrayList();
        scopes = Scopes.withDefault();
        globals = Scopes.empty();
    }

    @Override
    public String visit(AssertStmt assertStmt) {
        String condition = (String) visit(assertStmt.getCondition());
        return assertion(condition);
    }

    @Override
    public String visit(AssignStmt assignStmt) {
        String rhs = (String) visit(assignStmt.getExpr());
        String var = assignStmt.getVarRef().getVar();
        int id = scopes.updateVar(var);
        return SMTUtil.declare(var, id) + SMTUtil.assertion("=", var + id, rhs);
    }

    @Override
    public String visit(AssumeStmt assumeStmt) {
        String condition = (String) visit(assumeStmt.getCondition());
        return assume(condition);
    }

    @Override
    public String visit(BinaryExpr binaryExpr) {
        return SMTUtil.binaryOp(
            binaryExpr.getOperator(),
            (String) visit(binaryExpr.getLeft()),
            (String) visit(binaryExpr.getRight()));
    }

    @Override
    public String visit(BlockStmt blockStmt) {
        scopes.enterScope();
        List<String> statements =
            blockStmt.getStmts().stream()
                .map(x -> (String) visit(x))
                .collect(Collectors.toList());
        scopes.exitScope();
        return String.join("", statements);
    }

    @Override
    public String visit(CandidatePostcondition candidatePostcondition) {
        return null;
    }

    @Override
    public String visit(CandidatePrecondition candidatePrecondition) {
        return null;
    }

    @Override
    public String visit(HavocStmt havocStmt) {
        String var = havocStmt.getVarRef().getVar();
        return SMTUtil.declare(var, scopes.updateVar(var));
    }

    @Override
    public String visit(IfStmt ifStmt) {
        Scope scope = Scope.fromScope(scopes.topScope());
        String pred = SMTUtil.toBool((String) visit(ifStmt.getCondition()));

        Scope thenScope;
        if (scope.getPred().isEmpty()) {
            thenScope = Scope.fromScope(scope, pred);
        } else {
            thenScope = Scope.fromScope(
                scope,
                SMTUtil.toBool(SMTUtil.binaryOp("and", scope.getPred(), pred)));
        }
        scopes.enterScope(thenScope);
        String thenBlock = visit(ifStmt.getThenBlock());
        scopes.exitScope();

        Scope elseScope = Scope.fromScope(scope);
        String elseBlock = "";
        if (ifStmt.getElseBlock().isPresent()) {
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
            elseBlock = visit(ifStmt.getElseBlock().get());
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
    public String visit(NumberExpr numberExpr) {
        return SMTUtil.number(numberExpr.getNumber());
    }

    @Override
    public String visit(OldExpr oldExpr) {
        String var = visit(oldExpr.getVarRef());
        return var + globals.getId(var);
    }

    @Override
    public String visit(ParenExpr parenExpr) {
        return (String) visit(parenExpr.getExpr());
    }

    @Override
    public String visit(Postcondition postcondition) {
        postconditions.add((String) visit(postcondition.getCondition()));
        return "";
    }

    @Override
    public String visit(Precondition precondition) {
        return assume((String) visit(precondition.getCondition()));
    }

    @Override
    public String visit(ProcedureDecl procedureDecl) {
        StringBuilder result = new StringBuilder();
        scopes.enterScope();
        globals.enterScope(Scope.fromScope(scopes.topScope()));

        result.append(String.join("\n",
            procedureDecl.getParams().stream()
                .map(param -> SMTUtil.declare(param.getVar(), scopes.updateVar(param.getVar())))
                .collect(Collectors.toList())));

        result.append(String.join("\n",
            procedureDecl.getConditions().stream()
                .filter(cond -> cond instanceof Precondition)
                .map(cond -> (String) visit((Precondition) cond))
                .collect(Collectors.toList())));

        result.append(String.join("\n",
            procedureDecl.getStmts().stream()
                .map(stmt -> (String) visit(stmt))
                .collect(Collectors.toList())));

        String returnExpr = (String) visit(procedureDecl.getReturnExpr());
        result.append(String.join("\n",
            postconditions.stream()
                .map(p -> p.replace(RESULT_PLACEHOLDER, returnExpr))
                .collect(Collectors.toList())));

        scopes.exitScope();
        globals.exitScope();

        return result.toString();
    }

    @Override
    public String visit(Program program) {
        List<String> globals = program.getGlobalDecls().stream().map(this::visit).collect(Collectors.toList());
        List<String> procedures = program.getProcedureDecls().stream().map(this::visit).collect(Collectors.toList());
        String condition = SMTUtil.generateCondition(asserts);
        return String.join("", globals) + String.join("", procedures) + condition;
    }

    @Override
    public String visit(ResultExpr resultExpr) {
        return RESULT_PLACEHOLDER;
    }

    @Override
    public String visit(TernaryExpr ternaryExpr) {
        return SMTUtil.ternaryOp(
            SMTUtil.toBool((String) visit(ternaryExpr.getCondition())),
            (String) visit(ternaryExpr.getTrueExpr()),
            (String) visit(ternaryExpr.getFalseExpr()));
    }

    @Override
    public String visit(UnaryExpr unaryExpr) {
        return SMTUtil.unaryExpr(
            (String) visit(unaryExpr.getAtom()),
            unaryExpr.getOperators().stream().map(SMTUtil::unaryOp).collect(Collectors.toList()));
    }

    @Override
    public String visit(VarDeclStmt varDeclStmt) {
        String var = varDeclStmt.getVarRef().getVar();
        return SMTUtil.declare(var, scopes.getId(var));
    }

    @Override
    public String visit(VarRef varRef) {
        String var = varRef.getVar();
        return var + scopes.getId(var);
    }

    @Override
    public String visit(VarRefExpr varRefExpr) {
        return visit(varRefExpr.getVarRef());
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
}
