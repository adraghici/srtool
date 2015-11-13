package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;

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
    public List<Node> getChildren() {
        return Lists.newArrayList(condition);
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
