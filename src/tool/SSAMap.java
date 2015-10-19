package tool;

import java.util.HashMap;
import java.util.Map;

public class SSAMap {

    private Map<String, Integer> nextIDMap;
    private final Integer DEFAULT_ID = 0;

    public SSAMap() {
        nextIDMap = new HashMap<>();
    }

    public Integer getNextID(String var) {
        Integer nextID = DEFAULT_ID;

        if (nextIDMap.containsKey(var)) {
            nextID = nextIDMap.get(var) + 1;
            nextIDMap.replace(var, nextID);
        } else {
            nextIDMap.put(var, nextID);
        }

        return nextID;
    }

    public Integer getCurrentID(String var) {
        return nextIDMap.get(var);
    }
}
