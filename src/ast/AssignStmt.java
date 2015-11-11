package ast;

import java.util.List;

public class AssignStmt implements Stmt {
    private final VarRef varRef;
    private final Expr expr;

    public AssignStmt(VarRef varRef, Expr expr) {
        this.varRef = varRef;
        this.expr = expr;
    }

    public VarRef getVarRef() {
        return varRef;
    }

    public Expr getExpr() {
        return expr;
    }

    @Override
    public List<Node> getChildren() {
        return null;
    }
}
