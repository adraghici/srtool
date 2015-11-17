package ast;

import visitor.Visitor;

import java.util.Map;

public class ParenExpr implements AtomExpr {
    private final Expr expr;

    public ParenExpr(Expr expr) {
        this.expr = expr;
    }

    public Expr getExpr() {
        return expr;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Expr replace(Map<String, Expr> substitutes) {
        return new ParenExpr(getExpr().replace(substitutes));
    }
}
