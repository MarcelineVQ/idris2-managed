module Control.Monad.Managed

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Either

import System.File

-------------------------------------------------

-- See README.md

{-
Given some:

example : MonadManaged m => EitherT e m a

Your typical use will likely end up looking like this:
main = runManaged $ do
    Right x <- runEitherT example
      | Left y => ...
    ...
-- More examples at module bottom
-}
-------------------------------------------------

export
data Managed : Type -> Type where
  MkManaged : (1 _ : forall b. (a -> IO b) -> IO b) -> Managed a

getManaged : Managed a -> (forall b. (a -> IO b) -> IO b)
getManaged (MkManaged g) = g

export
%inline
managed : (1 _ : forall r. (a -> IO r) -> IO r) -> Managed a
managed = MkManaged

export
managed_ : (forall r. IO r -> IO r) -> Managed ()
managed_ f = managed $ \g => f (g ())

export
||| This can let you leak the resource through r, be very wary!
||| Best to avoid using.
manageWith : Managed a -> (a -> IO r) -> IO r
manageWith m = getManaged m

export
runManaged : Managed () -> IO ()
runManaged (MkManaged g) = g pure

public export
implementation Functor Managed where
  map f g = MkManaged $ \bmr => getManaged g (\a => bmr (f a))

public export
implementation Applicative Managed where
  pure x = MkManaged (\amr => amr x)
  f <*> x = MkManaged $ \bmr =>
   getManaged f (\ab => getManaged x (\a => bmr (ab a)))

public export
implementation Monad Managed where
  x >>= k = MkManaged $ \bmr => getManaged x (\a => getManaged (k a) bmr)

public export
Semigroup a => Semigroup (Managed a) where
  x <+> y = [| x <+> y |]

public export
Monoid a => Monoid (Managed a) where
  neutral = pure neutral

public export
implementation HasIO Managed where
  liftIO io = MkManaged (io >>=)

public export
interface HasIO m => MonadManaged m where
  use : Managed a -> m a -- bad name

public export
MonadManaged Managed where
  use = id

public export
MonadManaged m => MonadManaged (StateT s m) where
  use x = lift (use x)

public export
MonadManaged m => MonadManaged (EitherT e m) where
  use x = lift (use x)

-- Not in stdlib just yet
withFile' : HasIO io => String -> Mode -> (Either FileError File -> io a) -> io a
withFile' file mode act = do res <- openFile file mode
                             a <- act res
                             either (\_ => pure a)
                                    (\f => pure a <* closeFile f) res

managedFile : String -> Mode -> Managed (Either FileError File)
managedFile file mode = managed (withFile' file mode)

example : MonadManaged m => EitherT FileError m Nat
example = do f <- MkEitherT $ use (managedFile "/dev/urandom" Read)
             r <- MkEitherT $ liftIO $ fGetChars f 20
             pure (length r) -- '\0' ends Strings, this probably won't be 20!

example_main : IO ()
example_main = runManaged $ do
    Right x <- runEitherT example
      | Left y => liftIO (printLn y)
    putStrLn $ show x ++ " chars read from /dev/urandom"


ordering_test : IO ()
ordering_test = runManaged $ do
    managed $ (\f => f () <* printLn "release one")
    printLn 1
    managed $ (\f => f () <* printLn "release two")
    printLn 2
    managed $ (\f => f () <* printLn "release three")
    printLn 3
{-
   Assuming you've written your Managed action in a manner that 'releases' last,
   release is in reverse order of binding:
   :exec ordering_test
   1
   2
   3
   "release three"
   "release two"
   "release one"
-}
