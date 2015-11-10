package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class VarRef implements AtomExpr {
    private final String name;

    public VarRef(String name) {
        this.name = name;
    }

    private String getName() {
        return name;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList();
    }
}
