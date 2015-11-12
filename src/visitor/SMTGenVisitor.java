package visitor;

import ast.AssertStmt;
import ast.AssignStmt;
import ast.AssumeStmt;
import ast.BinaryExpr;
import ast.BlockStmt;
import ast.Expr;
import ast.HavocStmt;
import ast.IfStmt;
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
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import ssa.Scope;
import ssa.Scopes;
import tool.SMTUtil;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Visitor used to generated SMT code from an AST representation.
 */
public class SMTGenVisitor implements Visitor {
    public static final String RESULT_PLACEHOLDER = "RESULT?!";
    private final List<String> postconditions;
    private final List<String> assumptions;
    private final List<String> asserts;
    private final Scopes scopes;
    private final Scopes globals;

    public SMTGenVisitor() {
        postconditions = Lists.newArrayList();
        assumptions = Lists.newArrayList();
        asserts = Lists.newArrayList();
        scopes = Scopes.withDefault();
        globals = Scopes.empty();
    }

    @Override
    public String visit(Program program) {
        List<String> globals = program.getGlobalDecls().stream().map(this::visit).collect(Collectors.toList());
        List<String> procedures = program.getProcedureDecls().stream().map(this::visit).collect(Collectors.toList());
        String condition = SMTUtil.generateCondition(asserts);
        return String.join("", globals) + String.join("", procedures) + condition;
    }

    @Override
    public String visit(VarDeclStmt varDeclStmt) {
        String var = varDeclStmt.getVarRef().getVar();
        return SMTUtil.declare(var, scopes.getId(var));
    }

    @Override
    public String visit(ProcedureDecl procedureDecl) {
        StringBuilder result = new StringBuilder();
        scopes.enterScope();
        globals.enterScope(Scope.fromScope(scopes.topScope()));

        result.append(translateParams(procedureDecl.getParams()));
        result.append(translatePreConditions(procedureDecl.getConditions()));
        result.append(translateStatements(procedureDecl.getStmts()));
        result.append(translatePostConditions(procedureDecl.getConditions()));
        result.append(translateReturnExpression(procedureDecl.getReturnExpr()));

        scopes.exitScope();
        globals.exitScope();

        return result.toString();
    }

    @Override
    public String visit(Precondition precondition) {
        return assume((String) visit(precondition.getCondition()));
    }

    @Override
    public String visit(Postcondition postcondition) {
        postconditions.add((String) visit(postcondition.getCondition()));
        return "";
    }

    @Override
    public String visit(AssignStmt assignStmt) {
        String rhs = (String) visit(assignStmt.getExpr());
        String var = assignStmt.getVarRef().getVar();
        int id = scopes.updateVar(var);
        return SMTUtil.declare(var, id) + SMTUtil.assertion("=", var + id, rhs);
    }

    @Override
    public String visit(AssertStmt assertStmt) {
        String condition = (String) visit(assertStmt.getCondition());
        return assertion(condition);
    }

    @Override
    public String visit(AssumeStmt assumeStmt) {
        String condition = (String) visit(assumeStmt.getCondition());
        return assume(condition);
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

        Scope thenScope = createBranchScope(scope, pred, true);
        String thenBlock = translateBranch(thenScope, ifStmt.getThenBlock());

        Scope elseScope = Scope.fromScope(scope);
        String elseBlock = "";
        if (ifStmt.getElseBlock().isPresent()) {
            elseScope = createBranchScope(scope, pred, false);
            elseBlock = translateBranch(elseScope, ifStmt.getElseBlock().get());
        }

        StringBuilder endIf = new StringBuilder();
        Set<String> thenModset = ifStmt.getThenBlock().getModset();
        Set<String> elseModset = ifStmt.getElseBlock().map(BlockStmt::getModset).orElse(Collections.emptySet());
        for (String var : Sets.intersection(scope.vars(), ifStmt.getModset())) {
            endIf.append(SMTUtil.declare(var, scopes.updateVar(var)));
            String rhs = SMTUtil.ternaryOp(
                pred,
                var + getBranchId(scope, thenScope, thenModset, var),
                var + getBranchId(scope, elseScope, elseModset, var));
            endIf.append(SMTUtil.assertion("=", var + scopes.getId(var), rhs));
        }

        return thenBlock + elseBlock + endIf;
    }

    @Override
    public String visit(BlockStmt blockStmt) {
        scopes.enterScope();
        List<String> statements =
            blockStmt.getStmts().stream()
                .map(stmt -> (String) visit(stmt))
                .collect(Collectors.toList());
        scopes.exitScope();
        return String.join("", statements);
    }

    @Override
    public String visit(VarRef varRef) {
        String var = varRef.getVar();
        return var + scopes.getId(var);
    }

    @Override
    public String visit(TernaryExpr ternaryExpr) {
        return SMTUtil.ternaryOp(
            SMTUtil.toBool((String) visit(ternaryExpr.getCondition())),
            (String) visit(ternaryExpr.getTrueExpr()),
            (String) visit(ternaryExpr.getFalseExpr()));
    }

    @Override
    public String visit(BinaryExpr binaryExpr) {
        return SMTUtil.binaryOp(
            binaryExpr.getOperator(),
            (String) visit(binaryExpr.getLeft()),
            (String) visit(binaryExpr.getRight()));
    }

    @Override
    public String visit(UnaryExpr unaryExpr) {
        return SMTUtil.unaryExpr(
            (String) visit(unaryExpr.getAtom()),
            unaryExpr.getOperators().stream().map(SMTUtil::unaryOp).collect(Collectors.toList()));
    }

    @Override
    public String visit(NumberExpr numberExpr) {
        return SMTUtil.number(numberExpr.getNumber());
    }

    @Override
    public String visit(VarRefExpr varRefExpr) {
        return visit(varRefExpr.getVarRef());
    }

    @Override
    public String visit(ParenExpr parenExpr) {
        return (String) visit(parenExpr.getExpr());
    }

    @Override
    public String visit(ResultExpr resultExpr) {
        return RESULT_PLACEHOLDER;
    }

    @Override
    public String visit(OldExpr oldExpr) {
        String var = oldExpr.getVarRef().getVar();
        return var + globals.getId(var);
    }

    private String assertion(String expr) {
        Scope scope = scopes.topScope();
        if (scope.getPred().isEmpty()) {
            if (assumptions.isEmpty()) {
                asserts.add(expr);
            } else {
                asserts.add(SMTUtil.implies(
                    SMTUtil.toBool(SMTUtil.and(assumptions)), SMTUtil.toBool(expr)));
            }
        } else if (assumptions.isEmpty()) {
            asserts.add(SMTUtil.implies(scope.getPred(), SMTUtil.toBool(expr)));
        } else {
            asserts.add(SMTUtil.implies(
                SMTUtil.toBool(SMTUtil.and(
                    scope.getPred(),
                    SMTUtil.toBool(SMTUtil.and(assumptions)))),
                SMTUtil.toBool(expr)));
        }
        return "";
    }

    private String assume(String expr) {
        Scope scope = scopes.topScope();
        if (scope.getPred().isEmpty()) {
            assumptions.add(expr);
        } else {
            assumptions.add(SMTUtil.implies(scope.getPred(), SMTUtil.toBool(expr)));
        }
        return "";
    }

    private String translateBranch(Scope branchScope, BlockStmt blockStmt) {
        scopes.enterScope(branchScope);
        String block = visit(blockStmt);
        scopes.exitScope();
        return block;
    }

    private static Scope createBranchScope(Scope scope, String pred, boolean trueBranch) {
        String processedPred = trueBranch ? pred : SMTUtil.unaryOp("not", pred);
        if (scope.getPred().isEmpty()) {
            return Scope.fromScope(scope, processedPred);
        }
        return Scope.fromScope(scope, SMTUtil.toBool(SMTUtil.and(scope.getPred(), processedPred)));
    }

    private static int getBranchId(Scope currentScope, Scope branchScope, Set<String> modset, String var) {
        return modset.contains(var) ? branchScope.getId(var) : currentScope.getId(var);
    }

    private String translateParams(List<VarRef> params) {
        return String.join("",
            params.stream()
                .map(param -> SMTUtil.declare(param.getVar(), scopes.updateVar(param.getVar())))
                .collect(Collectors.toList()));
    }

    private String translatePreConditions(List<PrePostCondition> conditions) {
        return String.join("",
            conditions.stream()
                .filter(cond -> cond instanceof Precondition)
                .map(cond -> visit((Precondition) cond))
                .collect(Collectors.toList()));
    }

    private String translateStatements(List<Stmt> stmts) {
        return String.join("",
            stmts.stream()
                .map(stmt -> (String) visit(stmt))
                .collect(Collectors.toList()));
    }

    private String translatePostConditions(List<PrePostCondition> conditions) {
        return String.join("",
            conditions.stream()
                .filter(cond -> cond instanceof Postcondition)
                .map(cond -> visit((Postcondition) cond))
                .collect(Collectors.toList()));
    }

    private String translateReturnExpression(Expr returnExpr) {
        String returnExpression = (String) visit(returnExpr);
        return String.join("",
            postconditions.stream()
                .map(post -> assertion(post.replace(RESULT_PLACEHOLDER, returnExpression)))
                .collect(Collectors.toList()));
    }
}
