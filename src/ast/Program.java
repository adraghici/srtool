package ast;

import com.google.common.base.Strings;
import com.google.common.collect.Lists;
import visitor.PrintingVisitor;
import visitor.Visitor;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class Program implements Node {
    private List<Node> children;

    public Program(List<VarDeclStmt> globalDecls, List<ProcedureDecl> procedureDecls) {
        this.children = Lists.newArrayList(globalDecls);
        this.children.addAll(procedureDecls);
    }

    public List<VarDeclStmt> getGlobalDecls() {
        return children.stream()
            .filter(x -> x instanceof VarDeclStmt)
            .map(x -> (VarDeclStmt) x)
            .collect(Collectors.toList());
    }

    public List<ProcedureDecl> getProcedureDecls() {
        return children.stream()
            .filter(x -> x instanceof ProcedureDecl)
            .map(x -> (ProcedureDecl) x)
            .collect(Collectors.toList());
    }

    @Override
    public Set<String> getModified() {
        return getProcedureDecls().stream()
            .map(ProcedureDecl::getModified)
            .flatMap(Set::stream)
            .collect(Collectors.toSet());
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

    public String toString(Visitor visitor) {
        StringBuilder result = new StringBuilder();
        result.append(visitor.getDescription() + ":\n");
        result.append(new PrintingVisitor().visit(this));
        result.append(String.format("%s\n", Strings.repeat("-", 100)));
        return result.toString();
    }
}
