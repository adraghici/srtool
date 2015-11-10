package ast;

import java.util.List;

public class AssignStmt implements Stmt {
    private final String var;
    private final Expr expr;

    public AssignStmt(String var, Expr expr) {
        this.var = var;
        this.expr = expr;
    }

    public String getVar() {
        return var;
    }

    public Expr getExpr() {
        return expr;
    }

    @Override
    public List<Node> getChildren() {
        return null;
    }
}
