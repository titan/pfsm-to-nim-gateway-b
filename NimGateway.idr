module NimGateway

import Data.Maybe
import Data.List
import Data.List1
import Data.SortedMap
import Data.Strings
import System
import System.File

import Pfsm
import Pfsm.Analyser
import Pfsm.Checker
import Pfsm.Data
import Pfsm.Parser
import Pfsm.Nim
import Pfsm.Service2B

indentDelta : Nat
indentDelta = 2

record AppConfig where
  constructor MkAppConfig
  src : String
  middleware : String
  version: Bool

Show AppConfig where
  show (MkAppConfig src middleware version)
    = List.join "\n" [ "src: " ++ src
                     , "middleware: " ++ (show middleware)
                     , "version: " ++ (show version)
                     ]

middleware : String -> Maybe (List Meta) -> String
middleware defaultValue metas
  = case lookup "gateway.middleware" metas of
         Just (MVString m) => m
         _ => defaultValue

toNim : AppConfig -> Fsm -> String
toNim conf@(MkAppConfig _ mw _) fsm@(MkFsm _ _ _ _ _ _ _ metas)
  = let name = fsm.name
        pre = camelize (toNimName name)
        idfields = filter idFieldFilter fsm.model
        indexes = liftIndexes fsm.model fsm.metas
        searchFields = liftFullTextSearchFields fsm.model
        searchable = length searchFields > 0 in
        join "\n\n" $ List.filter nonblank [ generateImports $ referenced fsm.model
                                           , "const queue = " ++ (show (name ++ "-input"))
                                           , generateEventCalls pre name mw idfields fsm.events
                                           , generateGetJsonString pre name fsm.model
                                           , generateGetCollections pre name mw fsm.model indexes
                                           , generateGetObject pre name mw fsm
                                           , if searchable
                                                then generateFullTextSearch pre name mw searchFields
                                                else ""
                                           , generateRouters pre name fsm.transitions fsm.participants indexes searchable
                                           , generatePermissions pre name fsm.transitions fsm.participants indexes searchable
                                           ]
  where
    idFieldFilter : Parameter -> Bool
    idFieldFilter (_, _, ms)
      = case lookup "fsmid" ms of
             Just (MVString "calc") => True
             Just (MVString "copy") => True
             _ => False

    referenced : List Parameter -> List Name
    referenced ps
      = referenced' ps []
      where
        referenced' : List Parameter -> List Name -> List Name
        referenced' []                                       acc = acc
        referenced' ((_, (TRecord _ ps'), ms) :: xs)         acc = case lookup "reference" ms of
                                                                        Just (MVString dst) => referenced' xs ((dst :: acc) ++ (referenced ps'))
                                                                        _ => referenced' xs (acc ++ (referenced ps'))
        referenced' ((_, (TList (TRecord _ ps')), ms) :: xs) acc = case lookup "reference" ms of
                                                                        Just (MVString dst) => referenced' xs ((dst :: acc) ++ (referenced ps'))
                                                                        _ => referenced' xs (acc ++ (referenced ps'))
        referenced' ((_, _, ms) :: xs)                       acc = case lookup "reference" ms of
                                                                        Just (MVString dst) => referenced' xs (dst :: acc)
                                                                        _ => referenced' xs acc

    generateImports : List Name -> String
    generateImports refereds
      = List.join "\n" [ "import asyncdispatch, gatewayutils, httpbeauty, httpbeast, json, options, random, re, search_engine, sequtils, sets, sonic, strtabs, strutils, times"
                       , "import redis6 except `%`"
                       , List.join "\n" $ map (\x => "import " ++ (toNimName x)) refereds
                       ]

    generateEventCalls : String -> String -> String -> List Parameter -> List1 Event -> String
    generateEventCalls pre name defaultMiddleware idfields es
      = let fsmidcode = generateFsmId pre name idfields in
            List1.join "\n\n" $ map (generateEvent pre name fsmidcode) es
      where
        generateFsmId : String -> String -> List Parameter -> String
        generateFsmId pre name []
          = "generate_fsmid($tenant & \"-" ++ name ++ "-\" & $now())"
        generateFsmId pre name ((n, t, ms) :: [])
          = case lookup "fsmid" ms of
                 Just (MVString "copy") => toNimName n
                 _ => "generate_fsmid($tenant & \"-" ++ name ++ "-\" & $" ++ (toNimName n) ++ ")"
        generateFsmId pre name idfields
          = "generate_fsmid($tenant & \"-" ++ name ++ "-\" & " ++ (join " & " (map (\(n, t, _) => "$" ++ (toNimName n)) idfields)) ++ ")"

        generateEvent : String -> String -> String -> Event -> String
        generateEvent pre name fsmidcode evt@(MkEvent n ps ms)
          = let style = fsmIdStyleOfEvent evt
                mw = middleware defaultMiddleware ms in
                join "\n" $ List.filter nonblank [ "proc " ++ (toNimName n) ++ "*(request: Request, ctx: GatewayContext): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                                                 , if style == FsmIdStyleUrl then (indent indentDelta) ++ "var matches: array[1, string]" else ""
                                                 , if style == FsmIdStyleUrl then (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpPost and match(request.path.get(\"\"), re\"^\\/" ++ name ++ "\\/([0-9]+)\\/" ++ n ++ "$\", matches):" else (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpPost and request.path.get(\"\") == \"/" ++ name ++ "/" ++ n ++ "\":"
                                                 , generateMiddleware (indentDelta * 2) name fsmidcode n style mw ps
                                                 , (indent indentDelta) ++ "else:"
                                                 , (indent (indentDelta * 2)) ++ "result = none(ResponseData)"
                                                 ]

          where
            generateGetEventArgument : Nat -> Parameter -> String
            generateGetEventArgument idt (n, (TPrimType PTLong), _)  = let lhs = (indent idt) ++ (toNimName n)
                                                                           rhs = "data{\"" ++ n ++ "\"}.getStr(\"0\")" in
                                                                           lhs ++ " = " ++ rhs
            generateGetEventArgument idt (n, (TPrimType PTULong), _) = let lhs = (indent idt) ++ (toNimName n)
                                                                           rhs = "data{\"" ++ n ++ "\"}.getStr(\"0\")" in
                                                                           lhs ++ " = " ++ rhs
            generateGetEventArgument idt (n, (TList t), _)           = let lhs = (indent idt) ++ (toNimName n)
                                                                           rhs = "data{\"" ++ n ++ "\"}" in
                                                                           lhs ++ " = " ++ rhs
            generateGetEventArgument idt (n, (TDict k v), _)         = let lhs = (indent idt) ++ (toNimName n)
                                                                           rhs = "data{\"" ++ n ++ "\"}" in
                                                                           lhs ++ " = " ++ rhs
            generateGetEventArgument idt (n, (TRecord _ _), _)       = let lhs = (indent idt) ++ (toNimName n)
                                                                           rhs = "data{\"" ++ n ++ "\"}" in
                                                                           lhs ++ " = " ++ rhs
            generateGetEventArgument idt (n, t, _)                   = let lhs = (indent idt) ++ (toNimName n)
                                                                           rhs = toNimFromJson ("data{\"" ++ n ++ "\"}") t in
                                                                           lhs ++ " = " ++ rhs

            generateGetEventArguments : Nat -> List Parameter -> String
            generateGetEventArguments idt [] = ""
            generateGetEventArguments idt ps = List.join "\n" [ (indent idt) ++ "data = parseJson(request.body.get(\"{}\"))"
                                                              , List.join "\n" $ map (generateGetEventArgument idt) ps
                                                              ]

            generateSignatureBody : Nat -> List Parameter -> String
            generateSignatureBody idt ps
              = let items = map generateSignatureBody' $ sortBy (\(a, _, _), (b, _, _) => compare a b) ps in
                    if length items > Z
                       then (indent idt) ++ "signbody = @[" ++ (join ", " items) ++ "].join(\"&\")"
                       else (indent idt) ++ "signbody = \"\""
              where
                generateSignatureBody' : Parameter -> String
                generateSignatureBody' (n, (TPrimType PTString), _) = "\"" ++ n ++ "=\" & " ++ (toNimName n)
                generateSignatureBody' (n, (TPrimType PTLong), _)   = "\"" ++ n ++ "=\" & " ++ (toNimName n)
                generateSignatureBody' (n, (TPrimType PTULong), _)  = "\"" ++ n ++ "=\" & " ++ (toNimName n)
                generateSignatureBody' (n, (TList _), _)            = "\"" ++ n ++ "=\" & $ " ++ (toNimName n)
                generateSignatureBody' (n, (TDict _ _), _)          = "\"" ++ n ++ "=\" & $ " ++ (toNimName n)
                generateSignatureBody' (n, _,                    _) = "\"" ++ n ++ "=\" & $ " ++ (toNimName n)

            generateMainBody : Nat -> String -> String -> FsmIdStyle -> String -> List Parameter -> String
            generateMainBody idt fsmidcode n fsmIdStyle mw ps
              = let isInSession = isInfixOf "session" mw
                    idCode = case fsmIdStyle of
                                  FsmIdStyleUrl => "id.parseBiggestUInt"
                                  FsmIdStyleSession => "session"
                                  FsmIdStyleDomain => "domain"
                                  _ => fsmidcode
                    in
                    join "\n" $ List.filter nonblank [ (indent idt) ++ "let"
                                                     , (indent (idt + (indentDelta * 1))) ++ "callback = $rand(uint64)"
                                                     , (indent (idt + (indentDelta * 1))) ++ "fsmid = " ++ idCode

                                                     , (indent (idt + (indentDelta * 1))) ++ "args = {"
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"TENANT\": $tenant,"
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"DOMAIN\": $domain,"
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"GATEWAY\": ctx.gateway,"
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"TASK\": \"PLAY-EVENT\","
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"FSMID\": $fsmid,"
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"EVENT\": " ++ (show (toUpper n)) ++ ","
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"CALLBACK\": callback,"
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"OCCURRED-AT\": $to_mytimestamp(now()),"
                                                     , if isInSession then (indent (idt + (indentDelta * 2))) ++ "\"TRIGGER\": $session," else ""
                                                     , if length ps > 0 then (indent (idt + (indentDelta * 2))) ++ "\"PAYLOAD\": $data," else ""
                                                     , (indent (idt + (indentDelta * 1))) ++ "}"
                                                     , (indent idt) ++ "discard await ctx.queue_redis.xadd(queue, @args)"
                                                     , (indent idt) ++ "result = await check_result(ctx.cache_redis, tenant, callback, 0)"
                                                     ]

            generateMiddleware : Nat -> String -> String -> String -> FsmIdStyle -> String -> List Parameter -> String
            generateMiddleware idt name fsmidcode ename fsmIdStyle mw ps
              = let params = filter payloadParameterFilter ps in
                    join "\n" $ List.filter nonblank [ (indent idt) ++ "let"
                                                     , if fsmIdStyle == FsmIdStyleUrl then (indent (idt + (indentDelta * 1))) ++ "id = matches[0]" else ""
                                                     , generateGetEventArguments (idt + indentDelta) params
                                                     , generateSignatureBody (idt + indentDelta) params
                                                     , (indent idt) ++ "check_" ++ (toNimName mw) ++ "(request, ctx, \"POST|/" ++  (Data.List.join "/" (if fsmIdStyle == FsmIdStyleUrl then [name, "$2", ename] else [name, ename])) ++ (if fsmIdStyle == FsmIdStyleUrl then "|$1\" % [signbody, id], \"" ++ name ++ ":" ++ ename ++ "\"):" else "|\" & signbody, \"" ++ name ++ ":" ++ ename ++ "\"):")
                                                     , generateMainBody (idt + indentDelta) fsmidcode n fsmIdStyle mw params
                                                     ]

    generateGetJsonString : String -> String -> List Parameter -> String
    generateGetJsonString pre name params
      = let refs = filter referenceFilter params in
            List.join "\n" [ "proc get_" ++ (toNimName name) ++ "_json_string*(cache: AsyncRedis, tenant: string, fsmid: string): Future[Option[string]] {.async.} ="
                           , (indent indentDelta) ++ "let"
                           , (indent (indentDelta * 2)) ++ "key = \"tenant=\" & tenant & \"/" ++ name ++ "\""
                           , (indent (indentDelta * 2)) ++ "objopt = await cache.hget(key, fsmid)"
                           , (indent indentDelta) ++ "if objopt.isSome:"
                           , if length refs > 0
                                then List.join "\n" [ (indent (indentDelta * 2)) ++ "var refs: seq[(string, string)] = @[]"
                                                    , List.join "\n" $ map (generateGetReferenceJsonString (indentDelta * 2) name) refs
                                                    ]
                                else ""
                           , if length refs > 0
                                then (indent (indentDelta * 2)) ++ "result = some(\"{\\\"entity\\\":\" & objopt.get & \",\\\"ref\\\":{\" & refs.mapIt(\"\\\"\" & it[0] & \"\\\":\" & it[1]).join(\",\") & \"}}\")"
                                else (indent (indentDelta * 2)) ++ "result = some(\"{\\\"entity\\\":\" & objopt.get & \"}\")"
                           , (indent indentDelta) ++ "else:"
                           , (indent (indentDelta * 2)) ++ "result = none(string)"
                           ]
      where
        referenceFilter : Parameter -> Bool
        referenceFilter (_, _, metas)
          = case lookup "reference" metas of
                 Just (MVString _) => True
                 _                 => False

        generateGetReferenceJsonString : Nat -> String -> Parameter -> String
        generateGetReferenceJsonString idt parentName (n, TList _, ms)
          = let nimName = (toNimName n)
                refName = case lookup "reference" ms of
                               Just (MVString rn) => rn
                               _                  => ""
            in
                List.join "\n" [ (indent idt) ++ "let"
                               , (indent (idt + indentDelta)) ++ "ref_" ++ nimName ++ "_id_key = \"tenant=\" & $tenant & \"/" ++ parentName ++ "." ++ n ++ "\""
                               , (indent (idt + indentDelta)) ++ "ref_" ++ nimName ++ "_id_opt = await cache.hget(ref_" ++ nimName ++ "_id_key, fsmid)"
                               , (indent idt) ++ "if ref_" ++ nimName ++ "_id_opt.isSome:"
                               , (indent (idt + indentDelta)) ++ "var ref_" ++ nimName ++ "_collection: seq[(string, string)] = @[]"
                               , (indent (idt + indentDelta)) ++ "for ref_" ++ nimName ++ "_id in ref_" ++ nimName ++ "_id_opt.get.split('|'):"
                               , (indent (idt + indentDelta * 2)) ++ "let ref_" ++ nimName ++ "_opt = await get_" ++ (toNimName refName) ++ "_json_string(cache, $tenant, ref_" ++ nimName ++ "_id)"
                               , (indent (idt + indentDelta * 2)) ++ "if ref_" ++ nimName ++ "_opt.isSome:"
                               , (indent (idt + indentDelta * 3)) ++ "ref_" ++ nimName ++ "_collection.add((ref_" ++ nimName ++ "_id, ref_" ++ nimName ++ "_opt.get))"
                               , (indent (idt + indentDelta)) ++ "refs.add((\"" ++ n ++ "\", \"{\" & ref_" ++ nimName ++ "_collection.mapIt(\"\\\"\" & it[0] & \"\\\":\" & it[1]).join(\",\") & \"}\"))"
                ]
        generateGetReferenceJsonString idt parentName (n, t, ms)
          = let nimName = (toNimName n)
                refName = case lookup "reference" ms of
                               Just (MVString rn) => rn
                               _                  => ""
            in
                List.join "\n" [ (indent idt) ++ "let"
                               , (indent (idt + indentDelta)) ++ "ref_" ++ nimName ++ "_id_key = \"tenant=\" & $tenant & \"/" ++ parentName ++ "." ++ n ++ "\""
                               , (indent (idt + indentDelta)) ++ "ref_" ++ nimName ++ "_id_opt = await cache.hget(ref_" ++ nimName ++ "_id_key, fsmid)"
                               , (indent idt) ++ "if ref_" ++ nimName ++ "_id_opt.isSome:"
                               , (indent (idt + indentDelta)) ++ "let ref_" ++ nimName ++ "_opt = await get_" ++ (toNimName refName) ++ "_json_string(cache, $tenant, ref_" ++ nimName ++ "_id_opt.get)"
                               , (indent (idt + indentDelta)) ++ "if ref_" ++ nimName ++ "_opt.isSome:"
                               , (indent (idt + indentDelta * 2)) ++ "refs.add((\"" ++ n ++ "\", ref_" ++ nimName ++ "_opt.get))"
                ]


    generateGetObject : String -> String -> String -> Fsm -> String
    generateGetObject pre name defaultMiddleware fsm@(MkFsm _ _ _ _ _ _ _ metas)
      = let mw = middleware defaultMiddleware metas
            fsmIdStyle = fsmIdStyleOfFsm fsm in
            join "\n" $ List.filter nonblank [ "proc get_" ++ (toNimName name) ++ "*(request: Request, ctx: GatewayContext): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                                             , if fsmIdStyle == FsmIdStyleUrl then (indent indentDelta) ++ "var matches: array[1, string]" else ""
                                             , (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpGet and " ++ (if fsmIdStyle == FsmIdStyleUrl then "match(request.path.get(\"\"),  re\"^\\/" ++ name ++ "\\/([0-9]+)$\", matches):" else "request.path.get(\"\") == \"/" ++ name ++ "\":")
                                             , (indent (indentDelta * 2)) ++ "let"
                                             , if fsmIdStyle == FsmIdStyleUrl then (indent (indentDelta * 3)) ++ "id = matches[0]" else ""
                                             , (indent (indentDelta * 3)) ++ "signbody = \"\""
                                             , (indent (indentDelta * 2)) ++ if fsmIdStyle == FsmIdStyleSession || fsmIdStyle == FsmIdStyleDomain then ("check_signature_security_session(request, ctx, \"GET|/" ++ name ++ "|\" & signbody, \"\"):") else ("check_signature_security_session(request, ctx, \"GET|/" ++ name ++ "/$2|$1\" % [signbody, id], \"\"):")
                                             , (indent (indentDelta * 3)) ++ "let"
                                             , if fsmIdStyle == FsmIdStyleSession then (indent (indentDelta * 4)) ++ "id = $session" else ""
                                             , if fsmIdStyle == FsmIdStyleDomain then (indent (indentDelta * 4)) ++ "id = $domain" else ""
                                             , (indent (indentDelta * 4)) ++ "objopt = await get_" ++ (toNimName name) ++ "_json_string(ctx.cache_redis, $tenant, id)"
                                             , (indent (indentDelta * 3)) ++ "if objopt.isSome:"
                                             , (indent (indentDelta * 4)) ++ "let obj = objopt.get"
                                             , (indent (indentDelta * 4)) ++ "resp(\"{\\\"code\\\":200,\\\"payload\\\":\" & obj & \"}\", contentType = \"application/json;charset=utf8\")"
                                             , (indent (indentDelta * 3)) ++ "else:"
                                             , (indent (indentDelta * 4)) ++ "resp(\"{\\\"code\\\":404,\\\"payload\\\":\\\"Not Found\\\"}\", contentType = \"application/json;charset=utf8\")"
                                             , (indent indentDelta) ++ "else:"
                                             , (indent (indentDelta * 2)) ++ "result = none(ResponseData)"
                                             ]

    generateGetCollections : String -> String -> String -> List Parameter -> List Index -> String
    generateGetCollections pre name defaultMiddleware model indexes
      = List.join "\n\n" $ map (generateGetCollection pre name defaultMiddleware model) indexes
      where
        generateGetCollection : String -> String -> String -> List Parameter -> Index -> String
        generateGetCollection pre name defaultMiddleware model (MkIndex idxName fields)
          = let paramsCode = List.join ", " $ map (\(n, t, _) => (toNimName n) ++ ": " ++ (toNimType t)) fields
                urlpath = "/" ++ name ++ "/" ++ idxName in
                List.join "\n" [ "proc get_collection_of_" ++ (toNimName name) ++ "_by_" ++ (toNimName idxName)  ++ "*(request: Request, ctx: GatewayContext): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                               , (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpGet and (request.path.get(\"\") == \"" ++ urlpath ++ "\" or request.path.get(\"\").startsWith(\"" ++ urlpath ++ "\")):"
                               , (indent (indentDelta * 2)) ++ "let"
                               , (indent (indentDelta * 3)) ++ "params = request.params"
                               , (indent (indentDelta * 3)) ++ "offset = params.getOrDefault(\"offset\", \"0\")"
                               , (indent (indentDelta * 3)) ++ "limit = params.getOrDefault(\"limit\", \"10\")"
                               , List.join "\n" $ map ((indent (indentDelta * 3)) ++) $ map generateParsingParameter fields
                               , (indent (indentDelta * 3)) ++ "signbody = @[" ++ (List.join ", " $ sortBy (\a, b => compare a b) $ map (\x => "\"" ++ x ++ "=\" & " ++ (toNimName x)) $ ("limit" :: "offset" :: (map (\(n, _, _) => n) fields))) ++ "].join(\"&\")"
                               , (indent (indentDelta * 2)) ++ "check_" ++ (toNimName defaultMiddleware) ++ "(request, ctx, \"GET|" ++ urlpath ++ "|\" & signbody, \"" ++ name ++ ":get-collection-by-" ++ idxName ++ "\"):"
                               , (indent (indentDelta * 3)) ++ "let"
                               , (indent (indentDelta * 4)) ++ "offint = parseInt(offset)"
                               , (indent (indentDelta * 4)) ++ "limint = parseInt(limit)"
                               , (indent (indentDelta * 4)) ++ "srckey = \"tenant=\" & $tenant & \"/" ++ name ++ "\" & " ++ (List.join " & " $ map (\(n, _, _) => "\"/" ++ n ++ "=\" & " ++ (toNimName n)) fields)
                               , (indent (indentDelta * 4)) ++ "total = await ctx.cache_redis.zcard(srckey)"
                               , (indent (indentDelta * 4)) ++ "ids = await ctx.cache_redis.zrevrange(srckey, offint, offint + limint - 1)"
                               , (indent (indentDelta * 3)) ++ "var items: seq[string] = @[]"
                               , (indent (indentDelta * 3)) ++ "for id in ids:"
                               , (indent (indentDelta * 4)) ++ "let itemopt = await get_" ++ (toNimName name) ++ "_json_string(ctx.cache_redis, $tenant, id)"
                               , (indent (indentDelta * 4)) ++ "if itemopt.isSome:"
                               , (indent (indentDelta * 5)) ++ "items.add(itemopt.get)"
                               , (indent (indentDelta * 3)) ++ "resp(\"\"\"{\"code\":200,\"payload\":{\"pagination\":{\"total\":$2,\"offset\":$3,\"limit\":$4},\"data\":[$1]}}\"\"\" % [items.join \",\", $total, offset, limit], contentType = \"application/json;charset=utf8\")"
                               , (indent indentDelta) ++ "else:"
                               , (indent (indentDelta * 2)) ++ "result = none(ResponseData)"
                               ]
          where
            generateParsingParameter : Parameter -> String
            generateParsingParameter (n, _, _) = (toNimName n) ++ " = params.getOrDefault(\"" ++ n ++ "\", \"\")"

    generateFullTextSearch : String -> String -> String -> List Parameter -> String
    generateFullTextSearch pre name middleware searchFields
      = let urlpath = "" in
            List.join "\n" [ "proc search*(request: Request, ctx: GatewayContext): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                           , (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpPost and request.path.get(\"\") == \"" ++ urlpath ++ "\":"
                           , (indent (indentDelta * 2)) ++ "let"
                           , (indent (indentDelta * 3)) ++ "data = parseJson(request.body.get(\"{}\"))"
                           , (indent (indentDelta * 3)) ++ "offset = data{\"offset\"}.getInt"
                           , (indent (indentDelta * 3)) ++ "limit = data{\"limit\"}.getInt"
                           , (indent (indentDelta * 3)) ++ "query = data{\"query\"}.getStr"
                           , (indent (indentDelta * 3)) ++ "signbody = @[\"limit=\" & $limit, \"offset=\" & $offset, \"query=\" & query].join(\"&\")"
                           , (indent (indentDelta * 2)) ++ "check_" ++ (toNimName middleware) ++ "(request, ctx, \"POST|" ++ urlpath ++ "|\" & signbody, \"" ++ name ++ ":search\"):"
                           , (indent (indentDelta * 3)) ++ "let"
                           , (indent (indentDelta * 4)) ++ "sonic = await openAsync(ctx.metas.getOrDefault(\"sonic-host\"), ctx.metas.getOrDefault(\"sonic-port\").parseInt, ctx.metas.getOrDefault(\"sonic-passwd\"), SonicChannel.Search)"
                           , (indent (indentDelta * 4)) ++ "ids = await sonic.search(query)"
                           , (indent (indentDelta * 4)) ++ "total = len ids"
                           , (indent (indentDelta * 4)) ++ "key = \"tenant=\" & $tenant & \"/" ++ name ++ "\""
                           , (indent (indentDelta * 3)) ++ "asyncCheck sonic.quit"
                           , (indent (indentDelta * 3)) ++ "var objs: seq[string] = @[]"
                           , (indent (indentDelta * 3)) ++ "if offset < total:"
                           , (indent (indentDelta * 4)) ++ "var idx = 0"
                           , (indent (indentDelta * 4)) ++ "for id in ids:"
                           , (indent (indentDelta * 5)) ++ "if idx < offset:"
                           , (indent (indentDelta * 6)) ++ "idx += 1"
                           , (indent (indentDelta * 6)) ++ "continue"
                           , (indent (indentDelta * 5)) ++ "if idx > min(offset + limit, total):"
                           , (indent (indentDelta * 6)) ++ "break"
                           , (indent (indentDelta * 5)) ++ "let objopt = await get_" ++ (toNimName name) ++ "_json_string(ctx.cache_redis, $tenant, $id)"
                           , (indent (indentDelta * 5)) ++ "if objopt.isSome:"
                           , (indent (indentDelta * 6)) ++ "var obj = objopt.get"
                           , (indent (indentDelta * 6)) ++ "objs.add obj"
                           , (indent (indentDelta * 5)) ++ "idx += 1"
                           , (indent (indentDelta * 3)) ++ "resp(\"\"\"{\"code\":200,\"payload\":{\"pagination\":{\"total\":$2,\"offset\":$3,\"limit\":$4},\"data\":[$1]}}\"\"\" % [objs.join \",\", $total, $offset, $limit], contentType = \"application/json;charset=utf8\")"
                           , (indent indentDelta) ++ "else:"
                           , (indent (indentDelta * 2)) ++ "result = none(ResponseData)"
                           ]


    generateRouters : String -> String -> List1 Transition -> List1 Participant -> List Index -> Bool -> String
    generateRouters pre name transitions participants indexes searchable
      = List1.join "\n\n" $ map (generateRoutersOfParticipant pre name transitions indexes searchable) participants
      where
        generateCollectionRouters : Nat -> String -> String -> List Index -> List String
        generateCollectionRouters idt pre name indexes
          = map (generateCollectionRouter idt pre name) indexes
          where
            generateCollectionRouter : Nat -> String -> String -> Index -> String
            generateCollectionRouter idt pre name (MkIndex idxName _)
              = (indent idt) ++ "RouteProc[GatewayContext](" ++ (toNimName (name ++ ".get-collection-of-" ++ name ++ "-by-" ++ idxName)) ++ ")"

        generateEventRoutersByParticipantAndTransition : Nat -> String -> Participant -> Transition -> List String
        generateEventRoutersByParticipantAndTransition idt name p (MkTransition _ _ ts)
          = filter nonblank $ map (generateEventCallByParticipantAndTrigger idt name p) ts
          where
            generateEventCallByParticipantAndTrigger : Nat -> String -> Participant -> Trigger -> String
            generateEventCallByParticipantAndTrigger idt name p (MkTrigger ps e _ _)
              = if elemBy (==) p ps
                   then (indent idt) ++ "RouteProc[GatewayContext](" ++ (toNimName name) ++ "." ++ (toNimName (Event.name e)) ++ ")"
                   else ""

        generateRoutersOfParticipant : String -> String -> List1 Transition -> List Index -> Bool -> Participant -> String
        generateRoutersOfParticipant pre name transitions indexes searchable p@(MkParticipant n _)
          = let eventRouters = nub $ flatten $ List1.forget $ map (generateEventRoutersByParticipantAndTransition indentDelta name p) transitions
                collectionRouters = generateCollectionRouters indentDelta pre name indexes
                getObjRouter = (indent indentDelta) ++ "RouteProc[GatewayContext](" ++ (toNimName name) ++ ".get_" ++ (toNimName name) ++ ")"
                searchRouter = (indent indentDelta) ++ "RouteProc[GatewayContext](" ++ (toNimName name) ++ ".search)" in
                List.join "\n" [ "let " ++ (toNimName n) ++ "_routers*: seq[RouteProc[GatewayContext]] = @["
                               , List.join ",\n" ( eventRouters
                                                 ++ collectionRouters
                                                 ++ [getObjRouter]
                                                 ++ (if searchable
                                                        then [searchRouter]
                                                        else [])
                                                 )
                               , "]"
                               ]

    generatePermissions : String -> String -> List1 Transition -> List1 Participant -> List Index -> Bool -> String
    generatePermissions pre name transitions participants indexes searchable
      = List1.join "\n\n" $ map (generatePermissionsOfParticipant pre name transitions indexes) participants
      where
        generateEventPermissions : Nat -> String -> Participant -> Transition -> List String
        generateEventPermissions idt name p (MkTransition _ _ ts)
          = filter nonblank $ map (generateEventPermissionsByTrigger idt name p) ts
          where
            generateEventPermissionsByTrigger : Nat -> String -> Participant -> Trigger -> String
            generateEventPermissionsByTrigger idt name p (MkTrigger ps (MkEvent ename _ metas) _ _)
              = if elemBy (==) p ps
                   then (indent idt) ++ "(\"" ++ (displayName ename metas) ++ "\", " ++ (show (name ++ ":" ++ ename)) ++ ")"
                   else ""

        generateCollectionPermissions : Nat -> String -> String -> List Index -> List String
        generateCollectionPermissions idt pre name indexes
          = map (generateCollectionPermission idt pre name) indexes
          where
            generateCollectionPermission : Nat -> String -> String -> Index -> String
            generateCollectionPermission idt per name (MkIndex idxName _)
              = (indent idt) ++ "(\"获取列表\", " ++ (show (name ++ ":get-collection-by-" ++ idxName)) ++ ")"

        generatePermissionsOfParticipant : String -> String -> List1 Transition -> List Index -> Participant -> String
        generatePermissionsOfParticipant pre name transitions indexes p@(MkParticipant n _)
          = let eventPermissions = nub $ flatten $ List1.forget $ map (generateEventPermissions indentDelta name p) transitions
                collectionPermissions = generateCollectionPermissions indentDelta pre name indexes
                searchPermissions = (indent indentDelta) ++ "(\"搜索\", \"" ++ name ++ ":search\")" in
                List.join "\n" [ "let " ++ (toNimName n) ++ "_permissions*: seq[(string, string)] = @["
                               , List.join ",\n" ( eventPermissions
                                                 ++ collectionPermissions
                                                 ++ (if searchable
                                                        then [ searchPermissions ]
                                                        else [])
                                                 )
                               , "]"
                               ]

loadFsm : String -> Either String Fsm
loadFsm src
  = do (sexp, _) <- mapError parseErrorToString $ parseSExp src
       (fsm, _) <- mapError parseErrorToString $ analyse sexp
       fsm' <- mapError checkersErrorToString $ check fsm defaultCheckingRules
       pure fsm'

doWork : AppConfig -> IO ()
doWork conf
  = if conf.version
       then putStrLn "Version: B"
       else do Right fsm <- loadFsmFromFile conf.src
               | Left err => putStrLn $ show err
               putStrLn $ toNim conf fsm

parseArgs : List String -> Maybe AppConfig
parseArgs
  = parseArgs' Nothing Nothing False
  where
    parseArgs' : Maybe String -> Maybe String -> Bool -> List String -> Maybe AppConfig
    parseArgs' Nothing    _                 version []                 = if version then Just (MkAppConfig "" "signature-security-session" version) else Nothing
    parseArgs' (Just src) Nothing           version []                 = Just (MkAppConfig src "signature-security-session" version)
    parseArgs' (Just src) (Just middleware) version []                 = Just (MkAppConfig src middleware version)
    parseArgs' _          _                 _       []                 = Nothing
    parseArgs' src        _                 version ("-mw" :: x :: xs) = parseArgs' src (Just x) version xs
    parseArgs' src        middleware        _       ("-v" :: xs)       = parseArgs' src middleware True xs
    parseArgs' _          middleware        version (x :: xs)          = parseArgs' (Just x) middleware version xs

usage : String
usage
  = List.join "\n" [ "Usage: pfsm-to-nim-gateway [options] <src>"
                   , ""
                   , "Options:"
                   , "  -mv <middleware> Specify the default middleware to handle incoming requests."
                   , "                   Middlewares are:"
                   , "                   1. signature-security"
                   , "                   2. signature-security-session (default)"
                   , "                   3. signature-security-session-permission"
                   , "  -v               Show version"
                   ]

main : IO ()
main
  = do args <- getArgs
       case tail' args of
            Nothing => putStrLn usage
            Just args' => case parseArgs args' of
                               Just conf => doWork conf
                               Nothing => putStrLn usage
