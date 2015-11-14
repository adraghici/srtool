package visitor;

import ast.BlockStmt;
import ast.Node;
import ast.ProcedureDecl;
import ast.VarDeclStmt;
import ast.VarRef;
import ssa.Scopes;

/**
 * Visitor used to disambiguate variables within nested scopes.
 */
public class ShadowingVisitor implements Visitor {
    private final Scopes scopes;

    public ShadowingVisitor() {
        this.scopes = Scopes.withDefault();
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
        ProcedureDecl result = (ProcedureDecl) visitChildren(procedureDecl);
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
}
