package ast;

import visitor.VisitStage;
import visitor.Visitor;

import java.util.Optional;

public class CandidateInvariant implements LoopInvariant, TraceableNode {
    private final Expr condition;
    private final Optional<CandidateInvariant> source;
    private final VisitStage visitStage;

    public CandidateInvariant(
        Expr condition,
        Optional<CandidateInvariant> source,
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
    public Optional<CandidateInvariant> getSource() {
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
