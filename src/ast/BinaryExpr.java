package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;

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
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
