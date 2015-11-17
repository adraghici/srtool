package ast;

import visitor.Visitor;

import java.util.Map;

public class TernaryExpr implements Expr {
    private final Expr condition;
    private final Expr trueExpr;
    private final Expr falseExpr;

    public TernaryExpr(Expr condition, Expr trueExpr, Expr falseExpr) {
        this.condition = condition;
        this.trueExpr = trueExpr;
        this.falseExpr = falseExpr;
    }

    public Expr getCondition() {
        return condition;
    }

    public Expr getTrueExpr() {
        return trueExpr;
    }

    public Expr getFalseExpr() {
        return falseExpr;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Expr replace(Map<String, Expr> substitutes) {
        return new TernaryExpr(
            getCondition().replace(substitutes),
            getTrueExpr().replace(substitutes),
            getFalseExpr().replace(substitutes));
    }
}
