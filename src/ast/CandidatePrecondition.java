package ast;

import visitor.Visitor;

public class CandidatePrecondition implements PrePostCondition {
    private final Expr condition;

    public CandidatePrecondition(Expr condition) {
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
