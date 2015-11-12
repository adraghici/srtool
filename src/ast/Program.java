package ast;

import com.google.common.collect.Lists;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class Program implements Node {
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
        return procedureDecls.stream()
            .map(ProcedureDecl::getModified)
            .flatMap(Set::stream)
            .collect(Collectors.toSet());
    }

    @Override
    public List<Node> getChildren() {
        ArrayList<Node> children = Lists.newArrayList(globalDecls);
        children.addAll(procedureDecls);
        return children;
    }
}
