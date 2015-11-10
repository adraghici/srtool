package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class VarDeclStmt implements Stmt {
    private final String var;

    public VarDeclStmt(String var) {
        this.var = var;
    }

    public String getVar() {
        return var;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList();
    }
}
