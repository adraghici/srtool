package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;

public class Invariant implements LoopInvariant {
    private final Expr condition;
    private final List<Node> children;

    public Invariant(Expr condition) {
        this.condition = condition;
        this.children = Lists.newArrayList(condition);
    }

    @Override
    public Expr getCondition() {
        return condition;
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
