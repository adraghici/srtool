package ast;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import visitor.Visitor;

import java.util.List;
import java.util.Set;

public class HavocStmt implements Stmt {
    private List<Node> children;

    public HavocStmt(VarRef varRef) {
        this.children = Lists.newArrayList(varRef);
    }

    public VarRef getVarRef() {
        return (VarRef) children.get(0);
    }

    @Override
    public Set<String> getModified() {
        return Sets.newHashSet(getVarRef().getVar());
    }

    @Override public List<Node> getChildren() {
        return children;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
