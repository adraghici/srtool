package ast;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import java.util.List;
import java.util.Set;

public class VarRef implements Node {
    private final String var;

    public VarRef(String var) {
        this.var = var;
    }

    public String getVar() {
        return var;
    }

    @Override
    public Set<String> getModset() {
        return Sets.newHashSet();
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList();
    }
}
