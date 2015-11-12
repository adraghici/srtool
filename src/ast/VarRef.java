package ast;

public class VarRef implements Node {
    private final String var;

    public VarRef(String var) {
        this.var = var;
    }

    public String getVar() {
        return var;
    }
}
