package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;

public class CandidateInvariant implements LoopInvariant {
    private List<Node> children;

    public CandidateInvariant(Expr condition) {
        children = Lists.newArrayList(condition);
    }

    @Override
    public Expr getCondition() {
        return (Expr) children.get(0);
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(getCondition());
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
