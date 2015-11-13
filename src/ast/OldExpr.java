package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;

public class OldExpr implements AtomExpr {
    private List<Node> children;

    public OldExpr(VarRef varRef) {
        this.children = Lists.newArrayList(varRef);
    }

    public VarRef getVarRef() {
        return (VarRef) children.get(0);
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
