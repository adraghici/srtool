package ast;

import visitor.VisitStage;
import visitor.Visitor;

import java.util.Optional;

public class CandidatePostcondition implements PrePostCondition, TraceableNode {
    private final Expr condition;
    private final Optional<CandidatePostcondition> source;
    private final VisitStage visitStage;

    public CandidatePostcondition(
        Expr condition,
        Optional<CandidatePostcondition> source,
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
    public Optional<CandidatePostcondition> getSource() {
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
