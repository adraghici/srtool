package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;

public class ParenExpr implements AtomExpr {
    private List<Node> children;

    public ParenExpr(Expr expr) {
        this.children = Lists.newArrayList(expr);
    }

    public Expr getExpr() {
        return (Expr) children.get(0);
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
