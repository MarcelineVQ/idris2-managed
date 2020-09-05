Resource 
=====

Lifted pretty directly from Gabriel Gonzalez's lovely lib of the same name.  
I don't really want to lift so directly but there's really only one way to write this as it's just a restricted Codensity Monad which is just a restricted Cont Monad.  

A common pattern in resource usage is to have a wrapper that frees the resouce when you're done with it:
```idris
withFile : String -> (Either FileError File -> IO r) -> IO r
withSocket : ... -> (Either SocketError Socket -> IO r) -> IO r
withX : ... -> (X -> IO r) -> IO r
```
Inside of (X -> IO r) you have free use of the resource X and (if withX is written to) it is disposed of when you're done. However if you want to use more than one resource in this manner you end up nesting withX's and it can be quite a detriment to clean code.

Managed abstracts away the explicit nesting of withX when you want to work with more than one resource.
```idris
foo : IO ()
foo = do
    withFile filename $ \file ->
      withSocket fam ty num $ \socket -> do
        sendFileTo socket file
        ...
    ...
-- vs
foo : IO ()
foo = runManaged $ do
    file <- managed (withFile filename)
    soc <- managed (withSocket fam ty num)
    sendFileTo socket file
    ...
    
```


Version
-------

This package follows [Haskell PVP](https://pvp.haskell.org/) which is distinct from [SEMVER](https://semver.org/) in that when examining `1.2.3`, `1.2`  is the Major Version rather than `1`.
