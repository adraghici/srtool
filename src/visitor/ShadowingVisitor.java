package visitor;

import ast.*;
import ssa.Scopes;

import java.util.List;
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
    public Node visit(Program program) {
        List<VarDeclStmt> newGlobals = program.getGlobalDecls().stream()
            .map(global -> (VarDeclStmt) global.accept(this))
            .collect(Collectors.toList());
        List<ProcedureDecl> newProcedures = program.getProcedureDecls().stream()
            .map(procedure -> (ProcedureDecl) procedure.accept(this))
            .collect(Collectors.toList());
        return new Program(newGlobals, newProcedures);
    }

    @Override
    public Node visit(VarDeclStmt varDeclStmt) {
        VarRef varRef = varDeclStmt.getVarRef();
        scopes.declareVar(varRef.getVar());
        return new VarDeclStmt((VarRef) varRef.accept(this));
    }

    @Override
    public Node visit(ProcedureDecl procedureDecl) {
        scopes.enterScope();
        List<VarRef> newParams = procedureDecl.getParams().stream()
            .map(param -> (VarRef) param.accept(this))
            .collect(Collectors.toList());
        List<PrePostCondition> newConditions = procedureDecl.getConditions().stream()
            .map(cond -> (PrePostCondition) cond.accept(this))
            .collect(Collectors.toList());
        List<Stmt> newStmts = procedureDecl.getStmts().stream()
            .map(stmt -> (Stmt) stmt.accept(this))
            .collect(Collectors.toList());
        Expr newReturnExpr = (Expr) procedureDecl.getReturnExpr().accept(this);
        scopes.exitScope();
        return new ProcedureDecl(
            procedureDecl.getName(), newParams, newConditions, newStmts, newReturnExpr);
    }

    @Override
    public Node visit(BlockStmt blockStmt) {
        scopes.enterScope();
        List<Stmt> newStmts = blockStmt.getStmts().stream()
            .map(stmt -> (Stmt) stmt.accept(this))
            .collect(Collectors.toList());
        scopes.exitScope();
        return new BlockStmt(newStmts);
    }

    @Override
    public Node visit(VarRef varRef) {
        String var = varRef.getVar();
        String newVar = var + scopes.getId(var);
        return new VarRef(newVar);
    }
}
