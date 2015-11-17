package ast;

import visitor.Visitor;

import java.util.Optional;

public class CandidatePostcondition implements PrePostCondition, TraceableNode {
    private final Expr condition;
    private final Optional<CandidatePostcondition> source;
    private final SourceType sourceType;

    public CandidatePostcondition(
        Expr condition,
        Optional<CandidatePostcondition> source,
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
    public Optional<CandidatePostcondition> getSource() {
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
