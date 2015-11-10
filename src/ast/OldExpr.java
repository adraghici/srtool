package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class OldExpr implements AtomExpr {
    private final VarRef var;

    public OldExpr(VarRef var) {
        this.var = var;
    }

    private VarRef getVar() {
        return var;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList();
    }
}
