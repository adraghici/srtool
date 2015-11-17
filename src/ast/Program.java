package ast;

import com.google.common.base.Strings;
import visitor.PrintingVisitor;
import visitor.Visitor;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class Program implements Node {
    private List<Node> children;
    private final List<VarDeclStmt> globalDecls;
    private final List<ProcedureDecl> procedureDecls;

    public Program(List<VarDeclStmt> globalDecls, List<ProcedureDecl> procedureDecls) {
        this.globalDecls = globalDecls;
        this.procedureDecls = procedureDecls;
    }

    public List<VarDeclStmt> getGlobalDecls() {
        return globalDecls;
    }

    public List<ProcedureDecl> getProcedureDecls() {
        return procedureDecls;
    }

    @Override
    public Set<String> getModified() {
        return getProcedureDecls().stream()
            .map(ProcedureDecl::getModified)
            .flatMap(Set::stream)
            .collect(Collectors.toSet());
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
