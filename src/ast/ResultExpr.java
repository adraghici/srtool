package ast;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import java.util.List;
import java.util.Set;

public class ResultExpr implements AtomExpr {
    private final String token;

    public ResultExpr(String token) {
        this.token = token;
    }

    public String getToken() {
        return token;
    }

    @Override
    public Set<String> getModset() {
        return Sets.newHashSet();
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList();
    }
}
