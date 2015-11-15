package visitor;

import ast.*;
import ssa.Scope;
import ssa.Scopes;

/**
 * Visitor used to disambiguate variables within nested scopes.
 */
public class ShadowingVisitor implements Visitor {
    private final Scopes scopes;
    private final Scopes globals;

    public ShadowingVisitor() {
        this.scopes = Scopes.withDefault();
        globals = Scopes.empty();
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
        globals.enterScope(Scope.fromScope(scopes.topScope()));
        ProcedureDecl result = (ProcedureDecl) visitChildren(procedureDecl);
        globals.exitScope();
        scopes.exitScope();
        return result;
    }

    @Override
    public Node visit(BlockStmt blockStmt) {
        scopes.enterScope();
        BlockStmt result = (BlockStmt) visitChildren(blockStmt);
        scopes.exitScope();
        return result;
    }

    @Override
    public Node visit(VarRef varRef) {
        String var = varRef.getVar();
        String newVar = var + scopes.getId(var);
        return new VarRef(newVar);
    }

    @Override
    public Node visit(OldExpr oldExpr) {
        String var = oldExpr.getVarRef().getVar();
        return new OldExpr(new VarRef(var + globals.getId(var)));
    }
}
