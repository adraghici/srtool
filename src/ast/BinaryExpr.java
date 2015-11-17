package ast;

import visitor.Visitor;

import java.util.Map;

public class BinaryExpr implements Expr {
    private final String operator;
    private final Expr left;
    private final Expr right;

    public BinaryExpr(String operator, Expr left, Expr right) {
        this.operator = operator;
        this.left = left;
        this.right = right;
    }

    public String getOperator() {
        return operator;
    }

    public Expr getLeft() {
        return left;
    }

    public Expr getRight() {
        return right;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Expr replace(Map<String, Expr> substitutes) {
        return new BinaryExpr(getOperator(), getLeft().replace(substitutes), getRight().replace(
            substitutes));
    }
}
