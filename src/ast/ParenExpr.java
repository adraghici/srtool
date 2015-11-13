package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;

public class ParenExpr implements AtomExpr {
    private final Expr expr;
    private final List<Node> children;

    public ParenExpr(Expr expr) {
        this.expr = expr;
        this.children = Lists.newArrayList(expr);
    }

    public Expr getExpr() {
        return expr;
    }

    @Override
    public List<Node> getChildren() {
        return children;
    }

    @Override
    public void setChildren(List<Node> children) {
        children = Lists.newArrayList(children);
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
