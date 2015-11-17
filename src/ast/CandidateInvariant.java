package ast;

import visitor.Visitor;

public class CandidateInvariant implements LoopInvariant {
    private final Expr condition;

    public CandidateInvariant(Expr condition) {
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
