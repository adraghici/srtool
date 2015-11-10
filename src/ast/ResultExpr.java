package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class ResultExpr implements AtomExpr {
    private final String token;

    public ResultExpr(String token) {
        this.token = token;
    }

    private String getToken() {
        return token;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList();
    }
}
