package ast;

import visitor.Visitor;

public class Precondition implements PrePostCondition {
    private final Expr condition;

    public Precondition(Expr condition) {
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
