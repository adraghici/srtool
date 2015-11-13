package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;

public class UnaryExpr implements Expr {
    private final Expr atom;
    private final List<String> operators;
    private List<Node> children;

    public UnaryExpr(Expr atom, List<String> operators) {
        this.atom = atom;
        this.operators = operators;
        this.children = Lists.newArrayList(atom);
    }

    public Expr getAtom() {
        return atom;
    }

    public List<String> getOperators() {
        return operators;
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
