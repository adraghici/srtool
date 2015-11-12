package ast;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import java.util.List;
import java.util.Set;

public class Invariant implements LoopInvariant {
    private final Expr condition;

    public Invariant(Expr condition) {
        this.condition = condition;
    }

    @Override
    public Expr getCondition() {
        return condition;
    }

    @Override
    public Set<String> getModset() {
        return Sets.newHashSet();
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(condition);
    }
}
