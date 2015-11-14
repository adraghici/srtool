package ast;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import visitor.Visitor;

import java.util.List;
import java.util.Set;

public class VarDeclStmt implements Stmt {
    private List<Node> children;

    public VarDeclStmt(VarRef varRef) {
        this.children = Lists.newArrayList(varRef);
    }

    public VarRef getVarRef() {
        return (VarRef) children.get(0);
    }

    @Override
    public Set<String> getModified() {
        return Sets.newHashSet(getVarRef().getVar());
    }

    @Override
    public List<Node> getChildren() {
        return children;
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
