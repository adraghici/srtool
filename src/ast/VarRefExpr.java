package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;

public class VarRefExpr implements AtomExpr {
    private List<Node> children;

    public VarRefExpr(VarRef varRef) {
        this.children = Lists.newArrayList(varRef);
    }

    public VarRef getVarRef() {
        return (VarRef) children.get(0);
    }

    @Override
    public List<Node> getChildren() {
        return children;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
