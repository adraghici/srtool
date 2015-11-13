package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;

public class BinaryExpr implements Expr {
    private final String operator;
    private final Expr left;
    private final Expr right;
    private List<Node> children;

    public BinaryExpr(String operator, Expr left, Expr right) {
        this.operator = operator;
        this.left = left;
        this.right = right;
        this.children = Lists.newArrayList(left, right);
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
        return children;
    }

    @Override
    public void setChildren(List<Node> children) {
        this.children = Lists.newArrayList(children);
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
