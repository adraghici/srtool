package ast;

import visitor.Visitor;

public class Postcondition implements PrePostCondition {
    private final Expr condition;

    public Postcondition(Expr condition) {
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
