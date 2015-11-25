package visitor;

import ast.BlockStmt;
import ast.Node;
import ast.OldExpr;
import ast.ProcedureDecl;
import ast.VarDeclStmt;
import ast.VarRef;
import ssa.Scope;
import ssa.Scopes;
import tool.AssertCollector;

/**
 * Visitor used to disambiguate variables within nested scopes.
 */
public class ShadowingVisitor extends DefaultVisitor {
    private final Scopes scopes;
    private final Scopes globals;

    public ShadowingVisitor(AssertCollector assertCollector) {
        super(assertCollector);
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
        ProcedureDecl result = (ProcedureDecl) super.visit(procedureDecl);
        globals.exitScope();
        scopes.exitScope();
        return result;
    }

    @Override
    public Node visit(BlockStmt blockStmt) {
        scopes.enterScope();
        BlockStmt result = (BlockStmt) super.visit(blockStmt);
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

    @Override
    public String getDescription() {
        return "Shadowing visitor";
    }
}
