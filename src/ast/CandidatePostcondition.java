package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;

public class CandidatePostcondition implements PrePostCondition {
    private List<Node> children;

    public CandidatePostcondition(Expr condition) {
        this.children = Lists.newArrayList(condition);
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
    public void setChildren(List<Node> children) {
        this.children = Lists.newArrayList(children);
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
