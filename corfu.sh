# ./corfu_script.sh hw2a

tag=$(echo "acl2s_$1")
docker build -t $tag .
docker tag $tag $(echo "ankitku88/$tag")
docker push $(echo "ankitku88/$tag")


