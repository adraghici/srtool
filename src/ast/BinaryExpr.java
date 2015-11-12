package ast;

import com.google.common.collect.Lists;

import java.util.List;

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
    public List<Node> getChildren() {
        return Lists.newArrayList(left, right);
    }
}
