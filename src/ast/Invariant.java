package ast;

import visitor.Visitor;

public class Invariant implements LoopInvariant {
    private final Expr condition;

    public Invariant(Expr condition) {
        this.condition = condition;
    }

    @Override
    public Expr getCondition() {
        return condition;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
