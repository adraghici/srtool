package ast;

import visitor.Visitor;

import java.util.Optional;

public class CandidatePrecondition implements PrePostCondition, TraceableNode {
    private final Expr condition;
    private final Optional<CandidatePrecondition> source;
    private final SourceType sourceType;

    public CandidatePrecondition(
        Expr condition,
        Optional<CandidatePrecondition> source,
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
    public Optional<CandidatePrecondition> getSource() {
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
