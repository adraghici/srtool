package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;
import java.util.Map;

public class BinaryExpr implements Expr {
    private final String operator;
    private List<Node> children;

    public BinaryExpr(String operator, Expr left, Expr right) {
        this.operator = operator;
        this.children = Lists.newArrayList(left, right);
    }

    public String getOperator() {
        return operator;
    }

    public Expr getLeft() {
        return (Expr) children.get(0);
    }

    public Expr getRight() {
        return (Expr) children.get(1);
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

    @Override
    public Expr replace(Map<String, Expr> substitutes) {
        return new BinaryExpr(getOperator(), getLeft().replace(substitutes), getRight().replace(
            substitutes));
    }
}
