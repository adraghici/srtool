package ast;

import visitor.VisitStage;
import visitor.Visitor;

import java.util.Optional;

public class CandidatePrecondition implements PrePostCondition, TraceableNode {
    private final Expr condition;
    private final Optional<CandidatePrecondition> source;
    private final VisitStage visitStage;

    public CandidatePrecondition(
        Expr condition,
        Optional<CandidatePrecondition> source,
        VisitStage visitStage) {
        this.condition = condition;
        this.source = source;
        this.visitStage = visitStage;
    }

    @Override
    public Expr getCondition() {
        return condition;
    }

    @Override
    public Optional<CandidatePrecondition> getSource() {
        return source;
    }

    public VisitStage getVisitStage() {
        return visitStage;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
