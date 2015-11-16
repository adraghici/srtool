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
        List<String> globals = program.getGlobalDecls().stream()
            .map(g -> (String) g.accept(this))
            .collect(Collectors.toList());
        List<String> procedures = program.getProcedureDecls().stream()
            .map(p -> (String) p.accept(this))
            .collect(Collectors.toList());
        String condition = SMTUtil.generateCondition(asserts);

        return String.join("", globals) + String.join("", procedures) + condition + "\n(check-sat)\n" + SMTUtil.getValues(asserts.size());
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
        result.append(translatePreconditions(procedureDecl.getPreconditions()));
        result.append(translateStatements(procedureDecl.getStmts()));
        result.append(translatePostConditions(procedureDecl.getPostconditions()));
        result.append(translateReturnExpression(procedureDecl.getReturnExpr()));

        scopes.exitScope();
        globals.exitScope();

        assumptions.clear();
        postconditions.clear();

        return result.toString();
    }

    @Override
    public String visit(Precondition precondition) {
        return assume((String) precondition.getCondition().accept(this));
    }

    @Override
    public String visit(Postcondition postcondition) {
        postconditions.add((String) postcondition.getCondition().accept(this));
        return "";
    }

    @Override
    public String visit(AssignStmt assignStmt) {
        String rhs = (String) assignStmt.getExpr().accept(this);
        String var = assignStmt.getVarRef().getVar();
        int id = scopes.increaseVar(var);
        return SMTUtil.declare(var, id) + SMTUtil.assertion("=", var + id, rhs);
    }

    @Override
    public String visit(AssertStmt assertStmt) {
        String condition = (String) assertStmt.getCondition().accept(this);
        return assertion(condition);
    }

    @Override
    public String visit(AssumeStmt assumeStmt) {
        String condition = (String) assumeStmt.getCondition().accept(this);
        return assume(condition);
    }

    @Override
    public String visit(HavocStmt havocStmt) {
        String var = havocStmt.getVarRef().getVar();
        return SMTUtil.declare(var, scopes.increaseVar(var));
    }

    @Override
    public String visit(IfStmt ifStmt) {
        Scope scope = Scope.fromScope(scopes.topScope());
        String pred = SMTUtil.toBool((String) ifStmt.getCondition().accept(this));

        Scope thenScope = createBranchScope(scope, pred, true);
        String thenBlock = translateBranch(thenScope, ifStmt.getThenBlock());

        Scope elseScope = Scope.fromScope(scope);
        String elseBlock = "";
        if (ifStmt.getElseBlock().isPresent()) {
            elseScope = createBranchScope(scope, pred, false);
            elseBlock = translateBranch(elseScope, ifStmt.getElseBlock().get());
        }

        StringBuilder endIf = new StringBuilder();
        Set<String> thenModified = ifStmt.getThenBlock().getModified();
        Set<String> elseModified = ifStmt.getElseBlock().map(BlockStmt::getModified).orElse(Collections.emptySet());
        for (String var : scope.modset(ifStmt.getModified())) {
            endIf.append(SMTUtil.declare(var, scopes.increaseVar(var)));
            String rhs = SMTUtil.ternaryOp(
                pred,
                var + getBranchId(scope, thenScope, thenModified, var),
                var + getBranchId(scope, elseScope, elseModified, var));
            endIf.append(SMTUtil.assertion("=", var + scopes.getId(var), rhs));
        }

        return thenBlock + elseBlock + endIf;
    }

    @Override
    public String visit(BlockStmt blockStmt) {
        scopes.enterScope();
        List<String> statements =
            blockStmt.getStmts().stream()
                .map(stmt -> (String) stmt.accept(this))
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
            SMTUtil.toBool((String) ternaryExpr.getCondition().accept(this)),
            (String) ternaryExpr.getTrueExpr().accept(this),
            (String) ternaryExpr.getFalseExpr().accept(this));
    }

    @Override
    public String visit(BinaryExpr binaryExpr) {
        return SMTUtil.binaryOp(
            binaryExpr.getOperator(),
            (String) binaryExpr.getLeft().accept(this),
            (String) binaryExpr.getRight().accept(this));
    }

    @Override
    public String visit(UnaryExpr unaryExpr) {
        return SMTUtil.unaryExpr(
            (String) unaryExpr.getAtom().accept(this),
            unaryExpr.getOperators().stream().map(SMTUtil::unaryOp).collect(Collectors.toList()));
    }

    @Override
    public String visit(NumberExpr numberExpr) {
        return SMTUtil.number(numberExpr.getNumber());
    }

    @Override
    public String visit(VarRefExpr varRefExpr) {
        return (String) varRefExpr.getVarRef().accept(this);
    }

    @Override
    public String visit(ParenExpr parenExpr) {
        return (String) parenExpr.getExpr().accept(this);
    }

    @Override
    public String visit(ResultExpr resultExpr) {
        return resultExpr.getToken();
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
        String block = (String) blockStmt.accept(this);
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
        return String.join(
            "",
            params.stream()
                .map(param -> SMTUtil.declare(param.getVar(), scopes.increaseVar(param.getVar())))
                .collect(Collectors.toList()));
    }

    private String translatePreconditions(List<Precondition> conditions) {
        return String.join(
            "",
            conditions.stream().map(cond -> (String) cond.accept(this)).collect(Collectors.toList()));
    }

    private String translateStatements(List<Stmt> stmts) {
        return String.join(
            "",
            stmts.stream()
                .map(stmt -> (String) stmt.accept(this))
                .collect(Collectors.toList()));
    }

    private String translatePostConditions(List<Postcondition> conditions) {
        return String.join(
            "",
            conditions.stream().map(cond -> (String) cond.accept(this)).collect(Collectors.toList()));
    }

    private String translateReturnExpression(Expr returnExpr) {
        String returnExpression = (String) returnExpr.accept(this);
        return String.join(
            "",
            postconditions.stream()
                .map(post -> assertion(post.replace(SMTUtil.RESULT_PLACEHOLDER, returnExpression)))
                .collect(Collectors.toList()));
    }
}
