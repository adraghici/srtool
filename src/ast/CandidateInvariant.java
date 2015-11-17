package ast;

import visitor.Visitor;

import java.util.Optional;

public class CandidateInvariant implements LoopInvariant, TraceableNode {
    private final Expr condition;
    private final Optional<CandidateInvariant> source;
    private final SourceType sourceType;

    public CandidateInvariant(
        Expr condition,
        Optional<CandidateInvariant> source,
        SourceType sourceType) {
        this.condition = condition;
        this.source = source;
        this.sourceType = sourceType;
    }

    @Override
    public Expr getCondition() {
        return condition;
    }

    @Override
    public Optional<CandidateInvariant> getSource() {
        return source;
    }

    @Override
    public SourceType getSourceType() {
        return sourceType;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
